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

$pythonCommand = Get-Command python3 -ErrorAction SilentlyContinue
if (-not $pythonCommand) {
    $pythonCommand = Get-Command python -ErrorAction SilentlyContinue
}
if (-not $pythonCommand) {
    throw 'Python 3 was not found. It is required by the tracked-Lean shortcut scanner.'
}
$python = $pythonCommand.Source

Push-Location $projectRoot
try {
    & $lake build
    if ($LASTEXITCODE -ne 0) { throw "Lean build failed with exit code $LASTEXITCODE" }

    $scanner = 'workflows/verification/scan_tracked_lean.py'
    & $python $scanner --self-test
    if ($LASTEXITCODE -ne 0) {
        throw "The tracked-Lean scanner self-test failed with exit code $LASTEXITCODE"
    }

    & $python $scanner
    if ($LASTEXITCODE -ne 0) {
        throw "The tracked-Lean shortcut scan failed with exit code $LASTEXITCODE"
    }

    $knowledgeCheck = 'workflows/verification/check_knowledge.py'
    & $python $knowledgeCheck
    if ($LASTEXITCODE -ne 0) {
        throw "The knowledge consistency check failed with exit code $LASTEXITCODE"
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
    Write-Host 'PASS: kernel build, tracked-Lean scan, knowledge consistency, and exact-allowlist axiom audit succeeded.' -ForegroundColor Green
} finally {
    Pop-Location
}
