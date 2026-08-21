$ErrorActionPreference = 'Stop'
$projectRoot = Split-Path -Parent (Split-Path -Parent $PSScriptRoot)
$check = Join-Path $PSScriptRoot 'check.ps1'
$nativeProbe = Join-Path $projectRoot 'TheoryLib\GateProbe.lean'
$axiomProbe = Join-Path $projectRoot 'audit\GateProbe.lean'

function Invoke-ExpectedFailure([string[]] $Arguments, [string] $ExpectedText) {
    $previousPreference = $ErrorActionPreference
    $ErrorActionPreference = 'Continue'
    $output = & powershell.exe -NoProfile -ExecutionPolicy Bypass -File $check @Arguments 2>&1 | Out-String
    $exitCode = $LASTEXITCODE
    $ErrorActionPreference = $previousPreference
    if ($exitCode -eq 0) {
        throw "Verification gate unexpectedly accepted an exploit probe: $ExpectedText"
    }
    if ($output -notmatch [regex]::Escape($ExpectedText)) {
        Write-Host $output
        throw "Gate failed for an unexpected reason; wanted: $ExpectedText"
    }
    Write-Host "PASS: rejected probe containing $ExpectedText" -ForegroundColor Green
}

Push-Location $projectRoot
try {
    Set-Content -LiteralPath $nativeProbe -Encoding ascii -Value @'
import Mathlib
example : True := by native_decide
'@
    Invoke-ExpectedFailure @() 'native_decide'
    Remove-Item -Force -LiteralPath $nativeProbe

    Set-Content -LiteralPath $axiomProbe -Encoding ascii -Value @'
import Mathlib
axiom rewardHack : False
theorem fakeResolution : False := rewardHack
#print axioms fakeResolution
'@
    Invoke-ExpectedFailure @('-AuditFile', 'audit/GateProbe.lean') 'Non-allowlisted axiom detected: rewardHack'
    Remove-Item -Force -LiteralPath $axiomProbe

    & powershell.exe -NoProfile -ExecutionPolicy Bypass -File $check
    if ($LASTEXITCODE -ne 0) { throw 'Positive verification-gate control failed.' }
} finally {
    if (Test-Path -LiteralPath $nativeProbe) { Remove-Item -Force -LiteralPath $nativeProbe }
    if (Test-Path -LiteralPath $axiomProbe) { Remove-Item -Force -LiteralPath $axiomProbe }
    Pop-Location
}
