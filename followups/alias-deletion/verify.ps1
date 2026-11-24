param([Parameter(Mandatory = $true)][string]$ProjectLeanDirectory)
$ErrorActionPreference = 'Stop'
$sourceRoot = Join-Path $PSScriptRoot 'lean'
$priorLeanPath = $env:LEAN_PATH
$projectRoot = Split-Path -Parent (Resolve-Path -LiteralPath $ProjectLeanDirectory).Path
$revision = & git -C $projectRoot rev-parse HEAD
if ($LASTEXITCODE -ne 0 -or $revision.Trim() -ne '8ebf8f114c5d4568b533cb9864a4ea9b6ad5bbbc') {
    throw 'Use the pinned upstream checkout documented in README.md'
}
Push-Location -LiteralPath $ProjectLeanDirectory
try {
    $env:LEAN_PATH = $sourceRoot
    if ($priorLeanPath) { $env:LEAN_PATH += [IO.Path]::PathSeparator + $priorLeanPath }
    & lake build +PEqualNP.MetaComplexity.Helpers.EdgeFnModel
    if ($LASTEXITCODE -ne 0) { throw 'Dependency build failed' }
    & lake env lean "--root=$sourceRoot" -o (Join-Path $sourceRoot 'Boundary.olean') (Join-Path $sourceRoot 'Boundary.lean')
    if ($LASTEXITCODE -ne 0) { throw 'Boundary proof failed' }
    & lake env lean "--root=$sourceRoot" -o (Join-Path $sourceRoot 'AliasDeletion.olean') (Join-Path $sourceRoot 'AliasDeletion.lean')
    if ($LASTEXITCODE -ne 0) { throw 'Alias deletion proof failed' }
    & lake env lean "--root=$sourceRoot" (Join-Path $sourceRoot 'Example.lean')
    if ($LASTEXITCODE -ne 0) { throw 'Example proof failed' }
} finally {
    $env:LEAN_PATH = $priorLeanPath
    Pop-Location
}
