$ErrorActionPreference = 'Stop'
Set-Location -LiteralPath $PSScriptRoot
New-Item -ItemType Directory -Force -Path evidence | Out-Null
$checks = @(
  @{name='default_build'; command='lake'; arguments=@('build'); log='build.log'},
  @{name='fresh_background_source'; command='lake'; arguments=@('env','lean','-DwarningAsError=true','Kantorovich.lean'); log='fresh-background.log'},
  @{name='fresh_two_point_source'; command='lake'; arguments=@('env','lean','-DwarningAsError=true','Kantorovich/Stability.lean'); log='fresh-two-point.log'},
  @{name='fresh_certificates_source'; command='lake'; arguments=@('env','lean','-DwarningAsError=true','Kantorovich/ThreeCertificates.lean'); log='fresh-certificates.log'},
  @{name='fresh_three_point_source'; command='lake'; arguments=@('env','lean','-DwarningAsError=true','Kantorovich/ThreeStability.lean'); log='fresh-three-point.log'},
  @{name='fresh_examples_source'; command='lake'; arguments=@('env','lean','-DwarningAsError=true','Kantorovich/Examples.lean'); log='fresh-examples.log'},
  @{name='background_axiom_audit'; command='lake'; arguments=@('env','lean','-DwarningAsError=true','Audit.lean'); log='axioms-background.log'},
  @{name='stability_axiom_audit'; command='lake'; arguments=@('env','lean','-DwarningAsError=true','StabilityAudit.lean'); log='axioms-stability.log'},
  @{name='targeted_kernel_replay'; command='lake'; arguments=@('env','leanchecker','-v','Kantorovich','Kantorovich.Stability','Kantorovich.ThreeCertificates','Kantorovich.ThreeStability','Kantorovich.Examples'); log='kernel-replay.log'},
  @{name='exact_background_sanity'; command='python'; arguments=@('sanity_checks.py'); log='sanity-background.log'},
  @{name='exact_stability_sanity'; command='python'; arguments=@('stability_sanity.py'); log='sanity-stability.log'}
)
$results = @()
foreach ($check in $checks) {
  $started = [DateTime]::UtcNow.ToString('o')
  $commandArgs = $check.arguments
  $logPath = 'evidence/' + $check.log
  ('Command: ' + $check.command + ' ' + ($commandArgs -join ' ')) | Set-Content -LiteralPath $logPath -Encoding utf8
  ('Started UTC: ' + $started) | Add-Content -LiteralPath $logPath -Encoding utf8
  & $check.command @commandArgs 2>&1 | Tee-Object -FilePath $logPath -Append
  $commandExit = $LASTEXITCODE
  ('Exit code: ' + $commandExit) | Add-Content -LiteralPath $logPath -Encoding utf8
  $results += [ordered]@{
    name = $check.name
    command = $check.command
    arguments = $commandArgs
    started_at_utc = $started
    ended_at_utc = [DateTime]::UtcNow.ToString('o')
    exit_code = $commandExit
    log = $logPath
  }
  $results | ConvertTo-Json -Depth 6 | Set-Content -LiteralPath evidence/commands.json -Encoding utf8
  if ($commandExit -ne 0) { throw ($check.name + ' failed with exit ' + $commandExit) }
}
& ./record_release_evidence.ps1
