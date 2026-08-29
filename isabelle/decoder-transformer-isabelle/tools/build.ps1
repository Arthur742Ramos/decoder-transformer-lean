<#
.SYNOPSIS
  Build the Decoder_Transformer session with its pinned external AFP sessions.

.DESCRIPTION
  This wrapper delegates to the monorepo build tool.  Set
  DECODER_TRANSFORMER_AFP_ROOT to a directory containing Word_Lib and
  IEEE_Floating_Point, or to an AFP checkout whose sessions are under thys.
#>
[CmdletBinding()]
param(
  [string] $AfpRoot = $env:DECODER_TRANSFORMER_AFP_ROOT,
  [string] $IsabelleHome,
  [switch] $NoDocument,
  [switch] $Clean
)

$ErrorActionPreference = "Stop"

$projectDir = Split-Path -Parent $PSScriptRoot
$projectsDir = Split-Path -Parent $projectDir
$repoRoot = Split-Path -Parent $projectsDir
$repoBuild = Join-Path $repoRoot "tools\build.ps1"

if (-not (Test-Path -LiteralPath $repoBuild)) {
  throw "Cannot find the monorepo build wrapper: $repoBuild"
}
if ([string]::IsNullOrWhiteSpace($AfpRoot)) {
  throw "Set DECODER_TRANSFORMER_AFP_ROOT or pass -AfpRoot; see DEPENDENCIES.md."
}

$afpRootResolved = (Resolve-Path -LiteralPath $AfpRoot).Path
$searchRoots = @($afpRootResolved)
$thys = Join-Path $afpRootResolved "thys"
if (Test-Path -LiteralPath $thys) { $searchRoots += (Resolve-Path -LiteralPath $thys).Path }

function Find-AfpSession([string] $name) {
  foreach ($root in $searchRoots) {
    $candidate = Join-Path $root $name
    if (Test-Path -LiteralPath (Join-Path $candidate "ROOT")) {
      return (Resolve-Path -LiteralPath $candidate).Path
    }
  }
  throw "AFP session '$name' was not found below '$afpRootResolved'."
}

$extraDirs = @(
  (Find-AfpSession "Word_Lib"),
  (Find-AfpSession "IEEE_Floating_Point")
)

if (-not [string]::IsNullOrWhiteSpace($IsabelleHome)) {
  & $repoBuild -ProjectDir $projectDir -ExtraDir $extraDirs `
    -NoDocument:$NoDocument -Clean:$Clean -IsabelleHome $IsabelleHome
} else {
  & $repoBuild -ProjectDir $projectDir -ExtraDir $extraDirs `
    -NoDocument:$NoDocument -Clean:$Clean
}
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
