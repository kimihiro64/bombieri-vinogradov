$ErrorActionPreference = 'Stop'

$repositoryRoot = (Resolve-Path -LiteralPath (Join-Path $PSScriptRoot '..')).Path
$systemTempRoot = (Resolve-Path -LiteralPath ([IO.Path]::GetTempPath())).Path
$testRoot = Join-Path $systemTempRoot (
  'bombieri-vinogradov-release-licensing-' + [Guid]::NewGuid().ToString('N')
)
$documentationRoot = Join-Path $testRoot 'documentation'
$buildRoot = Join-Path $testRoot 'build'
New-Item -ItemType Directory -Path $documentationRoot -Force | Out-Null
New-Item -ItemType Directory -Path $buildRoot -Force | Out-Null

try {
  $documentationTargets = @(
    'index.html',
    'favicon.svg',
    'BombieriVinogradov.html',
    'references.html',
    'tactics.html'
  )
  $template = Join-Path $repositoryRoot 'assets/api-documentation-index.html'
  foreach ($relativePath in $documentationTargets) {
    $target = Join-Path $documentationRoot $relativePath
    $parent = Split-Path -Parent $target
    if (-not (Test-Path -LiteralPath $parent)) {
      New-Item -ItemType Directory -Path $parent -Force | Out-Null
    }
    Copy-Item -LiteralPath $template -Destination $target
  }

  $prepareDocumentation = Join-Path $repositoryRoot 'scripts/prepare-api-docs.ps1'
  & $prepareDocumentation -DocumentationRoot $documentationRoot

  $licensingRoot = Join-Path $documentationRoot 'licensing'
  $licensingIndex = Join-Path $licensingRoot 'index.html'
  foreach ($required in @(
    (Join-Path $documentationRoot 'index.html'),
    $licensingIndex,
    (Join-Path $licensingRoot 'BombieriVinogradov-Apache-2.0.txt'),
    (Join-Path $licensingRoot 'BombieriVinogradov-LICENSING.md')
  )) {
    if (-not (Test-Path -LiteralPath $required -PathType Leaf)) {
      throw "Prepared documentation is missing '$required'."
    }
  }

  $indexText = [IO.File]::ReadAllText($licensingIndex)
  $manifestPackages = foreach ($manifestPath in @(
    (Join-Path $repositoryRoot 'lake-manifest.json'),
    (Join-Path $repositoryRoot 'docbuild/lake-manifest.json')
  )) {
    (Get-Content -LiteralPath $manifestPath -Raw | ConvertFrom-Json).packages |
      Where-Object { $_.type -eq 'git' }
  }
  foreach ($package in $manifestPackages) {
    $encodedUrl = [Net.WebUtility]::HtmlEncode([string]$package.url)
    if ($indexText.IndexOf($encodedUrl, [StringComparison]::Ordinal) -lt 0) {
      throw "Licensing index omits dependency '$($package.url)'."
    }
  }
  if ($indexText.IndexOf('Lean 4 toolchain', [StringComparison]::Ordinal) -lt 0) {
    throw 'Licensing index omits the Lean 4 toolchain.'
  }

  $links = [regex]::Matches($indexText, 'href="\.\/([^"]+)"')
  foreach ($link in $links) {
    $target = Join-Path $licensingRoot $link.Groups[1].Value
    if (-not (Test-Path -LiteralPath $target -PathType Leaf)) {
      throw "Licensing index has a broken relative link '$($link.Groups[1].Value)'."
    }
  }

  $preparedHash = (Get-FileHash -LiteralPath $licensingIndex -Algorithm SHA256).Hash
  & $prepareDocumentation `
    -DocumentationRoot $documentationRoot `
    -UsePreparedLicensing
  $consumerHash = (Get-FileHash -LiteralPath $licensingIndex -Algorithm SHA256).Hash
  if ($consumerHash -cne $preparedHash) {
    throw 'Release-consumer validation rewrote the prepared licensing bundle.'
  }

  & (Join-Path $repositoryRoot 'scripts/prepare-release-licensing.ps1') `
    -DestinationRoot $buildRoot
  foreach ($required in @(
    (Join-Path $buildRoot 'LICENSE'),
    (Join-Path $buildRoot 'LICENSING.md'),
    (Join-Path $buildRoot 'licensing/index.html'),
    (Join-Path $buildRoot 'licensing/BombieriVinogradov-Apache-2.0.txt'),
    (Join-Path $buildRoot 'licensing/BombieriVinogradov-LICENSING.md')
  )) {
    if (-not (Test-Path -LiteralPath $required -PathType Leaf)) {
      throw "Prepared build archive is missing '$required'."
    }
  }

  Write-Host (
    "Release licensing smoke test passed for $($manifestPackages.Count) " +
      'manifest package entries.'
  )
} finally {
  if (Test-Path -LiteralPath $testRoot) {
    $resolvedTestRoot = (Resolve-Path -LiteralPath $testRoot).Path
    $tempPrefix = $systemTempRoot.TrimEnd(
      [IO.Path]::DirectorySeparatorChar,
      [IO.Path]::AltDirectorySeparatorChar
    ) + [IO.Path]::DirectorySeparatorChar
    $expectedLeaf = 'bombieri-vinogradov-release-licensing-'
    if (-not $resolvedTestRoot.StartsWith(
        $tempPrefix,
        [StringComparison]::OrdinalIgnoreCase
      ) -or -not (Split-Path -Leaf $resolvedTestRoot).StartsWith(
        $expectedLeaf,
        [StringComparison]::Ordinal
      )) {
      throw "Refusing to remove unexpected smoke-test path: $resolvedTestRoot"
    }
    Remove-Item -LiteralPath $resolvedTestRoot -Recurse -Force
  }
}
