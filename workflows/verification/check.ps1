param(
    [string] $AuditFile = 'audit/AxiomAudit.lean'
)

$ErrorActionPreference = 'Stop'

$projectRoot = Split-Path -Parent (Split-Path -Parent $PSScriptRoot)
$lakeCommand = Get-Command lake -ErrorAction SilentlyContinue
if ($lakeCommand) {
    $lake = $lakeCommand.Source
} else {
    $lake = Join-Path $env:USERPROFILE '.elan\bin\lake.exe'
}

if (-not (Test-Path -LiteralPath $lake)) {
    throw 'Lake was not found. Install Lean with Elan and reopen the terminal.'
}

Push-Location $projectRoot
try {
    & $lake build
    if ($LASTEXITCODE -ne 0) { throw "Lean build failed with exit code $LASTEXITCODE" }

    $forbidden = Get-ChildItem -LiteralPath 'TheoryLib' -Recurse -Filter '*.lean' |
        Select-String -Pattern '\b(sorry|admit|native_decide|sorryAx|Lean\.ofReduceBool|Lean\.trustCompiler)\b|^\s*(axiom|opaque|constant|unsafe)\b'
    if ($forbidden) {
        $forbidden | ForEach-Object { Write-Error "$($_.Path):$($_.LineNumber): $($_.Line)" }
        throw 'Forbidden placeholder, axiom, or compiler-trusting shortcut found in the verified Lean track.'
    }

    $auditOutput = (& $lake env lean $AuditFile 2>&1 | Out-String)
    if ($LASTEXITCODE -ne 0) {
        Write-Host $auditOutput
        throw 'The explicit axiom audit did not compile.'
    }

    $allowedAxioms = [System.Collections.Generic.HashSet[string]]::new(
        [string[]]@('propext', 'Classical.choice', 'Quot.sound'),
        [System.StringComparer]::Ordinal
    )
    $dependencyLists = [regex]::Matches($auditOutput, 'depends on axioms:\s*\[([^\]]*)\]')
    if ($dependencyLists.Count -eq 0 -and $auditOutput -notmatch 'does not depend on any axioms') {
        Write-Host $auditOutput
        throw 'The axiom audit produced no parseable theorem result.'
    }
    foreach ($dependencyList in $dependencyLists) {
        $names = $dependencyList.Groups[1].Value -split ',' |
            ForEach-Object { $_.Trim() } |
            Where-Object { $_ }
        foreach ($name in $names) {
            if (-not $allowedAxioms.Contains($name)) {
                Write-Host $auditOutput
                throw "Non-allowlisted axiom detected: $name"
            }
        }
    }

    Write-Host $auditOutput
    Write-Host 'PASS: kernel build, exploit scan, and exact-allowlist axiom audit succeeded.' -ForegroundColor Green
} finally {
    Pop-Location
}
