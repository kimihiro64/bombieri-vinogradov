param(
  [Parameter(Mandatory = $true)]
  [string]$DestinationRoot,

  [switch]$IncludeDependencyLicenses
)

$ErrorActionPreference = 'Stop'

$projectName = 'Bombieri-Vinogradov in Lean'
$projectStem = 'BombieriVinogradov'
$repositoryRoot = (Resolve-Path -LiteralPath (Join-Path $PSScriptRoot '..')).Path
$destination = (Resolve-Path -LiteralPath $DestinationRoot).Path
$destinationPrefix = $destination.TrimEnd(
  [IO.Path]::DirectorySeparatorChar,
  [IO.Path]::AltDirectorySeparatorChar
) + [IO.Path]::DirectorySeparatorChar
$licensingRoot = Join-Path $destination 'licensing'
$licensingFullPath = [IO.Path]::GetFullPath($licensingRoot)
if (-not $licensingFullPath.StartsWith(
    $destinationPrefix,
    [StringComparison]::OrdinalIgnoreCase
  )) {
  throw "Licensing output escapes the requested destination: $licensingFullPath"
}

if (Test-Path -LiteralPath $licensingFullPath) {
  $resolvedExisting = (Resolve-Path -LiteralPath $licensingFullPath).Path
  if (-not $resolvedExisting.StartsWith(
      $destinationPrefix,
      [StringComparison]::OrdinalIgnoreCase
    )) {
    throw "Refusing to replace licensing output outside the destination: $resolvedExisting"
  }
  Remove-Item -LiteralPath $resolvedExisting -Recurse -Force
}
New-Item -ItemType Directory -Path $licensingFullPath | Out-Null

$projectLicenseSource = Join-Path $repositoryRoot 'LICENSE'
$projectScopeSource = Join-Path $repositoryRoot 'LICENSING.md'
foreach ($source in @($projectLicenseSource, $projectScopeSource)) {
  if (-not (Test-Path -LiteralPath $source -PathType Leaf)) {
    throw "Required project licensing source is missing: $source"
  }
}
Copy-Item -LiteralPath $projectLicenseSource `
  -Destination (Join-Path $destination 'LICENSE') -Force
Copy-Item -LiteralPath $projectScopeSource `
  -Destination (Join-Path $destination 'LICENSING.md') -Force

$projectLicenseName = "$projectStem-Apache-2.0.txt"
$projectScopeName = "$projectStem-LICENSING.md"
Copy-Item -LiteralPath (Join-Path $repositoryRoot 'LICENSE') `
  -Destination (Join-Path $licensingFullPath $projectLicenseName)
Copy-Item -LiteralPath (Join-Path $repositoryRoot 'LICENSING.md') `
  -Destination (Join-Path $licensingFullPath $projectScopeName)

$entries = [Collections.Generic.List[object]]::new()
$entries.Add([PSCustomObject]@{
  Name = $projectName
  Source = 'This repository'
  Revision = 'Release commit'
  Files = @($projectLicenseName, $projectScopeName)
})

if ($IncludeDependencyLicenses) {
  $gitCandidates = @(
    Get-Command git -CommandType Application -ErrorAction Stop |
      Sort-Object Source -Unique
  )
  $leanCandidates = @(
    Get-Command lean -CommandType Application -ErrorAction Stop |
      Sort-Object Source -Unique
  )
  if ($gitCandidates.Count -lt 1 -or $leanCandidates.Count -lt 1) {
    throw 'Unable to resolve Git and Lean executables for dependency licensing.'
  }
  $gitPath = $gitCandidates[0].Source
  $leanPath = $leanCandidates[0].Source
  if (-not (Test-Path -LiteralPath $gitPath -PathType Leaf) -or
      -not (Test-Path -LiteralPath $leanPath -PathType Leaf)) {
    throw 'Resolved Git or Lean executable is not a regular file.'
  }
  $packagesRoot = (Resolve-Path -LiteralPath (Join-Path $repositoryRoot '.lake/packages')).Path

  function Normalize-GitUrl([string]$Url) {
    return ($Url.Trim().TrimEnd('/') -replace '\.git$', '').ToLowerInvariant()
  }

  $packageDirectoriesByUrl = @{}
  foreach ($directory in Get-ChildItem -LiteralPath $packagesRoot -Directory) {
    $remote = (& $gitPath -C $directory.FullName config --get remote.origin.url 2>$null)
    if ($LASTEXITCODE -eq 0 -and -not [string]::IsNullOrWhiteSpace($remote)) {
      $packageDirectoriesByUrl[(Normalize-GitUrl $remote)] = $directory.FullName
    }
  }

  $packagesByIdentity = [ordered]@{}
  foreach ($manifestPath in @(
    (Join-Path $repositoryRoot 'lake-manifest.json'),
    (Join-Path $repositoryRoot 'docbuild/lake-manifest.json')
  )) {
    $manifest = Get-Content -LiteralPath $manifestPath -Raw | ConvertFrom-Json
    foreach ($package in $manifest.packages | Where-Object { $_.type -eq 'git' }) {
      $identity = "$(Normalize-GitUrl $package.url)@$($package.rev)"
      if (-not $packagesByIdentity.Contains($identity)) {
        $packagesByIdentity[$identity] = $package
      }
    }
  }

  $dependenciesRoot = Join-Path $licensingFullPath 'dependencies'
  New-Item -ItemType Directory -Path $dependenciesRoot | Out-Null
  foreach ($package in $packagesByIdentity.Values) {
    $normalizedUrl = Normalize-GitUrl $package.url
    if (-not $packageDirectoriesByUrl.ContainsKey($normalizedUrl)) {
      throw "Cannot locate the checked-out package for $($package.url). Run lake update first."
    }
    $packageDirectory = $packageDirectoriesByUrl[$normalizedUrl]
    $displayName = [string]$package.name
    $safeName = ($displayName -replace '[^A-Za-z0-9._-]', '')
    if ([string]::IsNullOrWhiteSpace($safeName)) {
      throw "Cannot derive a safe licensing directory for package '$displayName'."
    }
    $packageOutput = Join-Path $dependenciesRoot $safeName
    New-Item -ItemType Directory -Path $packageOutput | Out-Null
    $notices = @(
      Get-ChildItem -LiteralPath $packageDirectory -Force -File |
        Where-Object { $_.Name -match '^(LICENSE|LICENCE|COPYING|NOTICE)(S)?(?:\.|$)' }
    )
    if ($notices.Count -eq 0) {
      throw "Package '$displayName' has no top-level licence or notice file."
    }
    foreach ($notice in $notices) {
      Copy-Item -LiteralPath $notice.FullName -Destination $packageOutput
    }
    $entries.Add([PSCustomObject]@{
      Name = $displayName
      Source = [string]$package.url
      Revision = [string]$package.rev
      Files = @($notices | ForEach-Object { "dependencies/$safeName/$($_.Name)" })
    })
  }

  $leanPrefixText = (& $leanPath --print-prefix)
  if ($LASTEXITCODE -ne 0 -or [string]::IsNullOrWhiteSpace($leanPrefixText)) {
    throw 'Unable to resolve the active Lean toolchain prefix.'
  }
  $leanPrefix = (Resolve-Path -LiteralPath $leanPrefixText.Trim()).Path
  $leanOutput = Join-Path $dependenciesRoot 'Lean4'
  New-Item -ItemType Directory -Path $leanOutput | Out-Null
  $leanNotices = @(
    Get-ChildItem -LiteralPath $leanPrefix -Force -File |
      Where-Object { $_.Name -match '^(LICENSE|LICENCE|COPYING|NOTICE)(S)?(?:\.|$)' }
  )
  if ($leanNotices.Count -eq 0) {
    throw "Lean toolchain at '$leanPrefix' has no top-level licence or notice file."
  }
  foreach ($notice in $leanNotices) {
    Copy-Item -LiteralPath $notice.FullName -Destination $leanOutput
  }
  $leanVersion = ((& $leanPath --version) -join ' ').Trim()
  $entries.Add([PSCustomObject]@{
    Name = 'Lean 4 toolchain'
    Source = $leanVersion
    Revision = 'Selected by lean-toolchain'
    Files = @($leanNotices | ForEach-Object { "dependencies/Lean4/$($_.Name)" })
  })
}

function ConvertTo-HtmlText([string]$Text) {
  return [Net.WebUtility]::HtmlEncode($Text)
}

$rows = foreach ($entry in $entries) {
  $links = foreach ($file in $entry.Files) {
    $encodedFile = ConvertTo-HtmlText ($file -replace '\\', '/')
    '<a href="./{0}">{0}</a>' -f $encodedFile
  }
  '<tr><td>{0}</td><td><code>{1}</code></td><td><code>{2}</code></td><td>{3}</td></tr>' -f `
    (ConvertTo-HtmlText $entry.Name), `
    (ConvertTo-HtmlText $entry.Source), `
    (ConvertTo-HtmlText $entry.Revision), `
    ($links -join '<br>')
}

$document = @"
<!doctype html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>$projectName licensing</title>
  <style>
    body { max-width: 1100px; margin: 2rem auto; padding: 0 1rem; font: 16px/1.5 system-ui, sans-serif; }
    table { width: 100%; border-collapse: collapse; }
    th, td { border: 1px solid #999; padding: .6rem; text-align: left; vertical-align: top; }
    code { overflow-wrap: anywhere; }
  </style>
</head>
<body>
  <h1>$projectName licensing</h1>
  <p>The repository's original material is Apache-2.0 by default. The research paper is also offered under CC-BY-4.0. Mathematical provenance and copyright licensing are separate. See <a href="./$projectScopeName">the complete scope statement</a>.</p>
  <h2>Included notices</h2>
  <table>
    <thead><tr><th>Component</th><th>Source</th><th>Revision</th><th>Licence and notice files</th></tr></thead>
    <tbody>
$($rows -join "`n")
    </tbody>
  </table>
</body>
</html>
"@
[IO.File]::WriteAllText((Join-Path $licensingFullPath 'index.html'), $document)

Write-Host "Prepared licensing information for $($entries.Count) component(s)."
