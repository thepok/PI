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

    # Scan every tracked project-owned Lean file, not only TheoryLib/.  This
    # includes the root import surface, the explicit audit, and any future
    # Lean source added elsewhere, while excluding untracked build products
    # and dependency checkouts under .lake/.
    $trackedLeanPaths = @(& git ls-files -- '*.lean')
    if ($LASTEXITCODE -ne 0) {
        throw 'Could not enumerate tracked Lean files with git ls-files.'
    }
    if ($trackedLeanPaths.Count -eq 0) {
        throw 'The repository contains no tracked Lean files to verify.'
    }

    $trackedLeanFiles = $trackedLeanPaths | ForEach-Object {
        if (-not (Test-Path -LiteralPath $_ -PathType Leaf)) {
            throw "Tracked Lean file is missing from the checkout: $_"
        }
        Get-Item -LiteralPath $_
    }

    Write-Host "Scanning $($trackedLeanPaths.Count) tracked Lean files for forbidden trust shortcuts."
    $forbidden = $trackedLeanFiles |
        Select-String -Pattern '\b(sorry|admit|native_decide|sorryAx|Lean\.ofReduceBool|Lean\.trustCompiler)\b|^\s*(axiom|opaque|constant|unsafe)\b'
    if ($forbidden) {
        $forbidden | ForEach-Object { Write-Error "$($_.Path):$($_.LineNumber): $($_.Line)" }
        throw 'Forbidden placeholder, axiom, or compiler-trusting shortcut found in tracked Lean source.'
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
    Write-Host 'PASS: kernel build, all-tracked-Lean exploit scan, and exact-allowlist axiom audit succeeded.' -ForegroundColor Green
} finally {
    Pop-Location
}
