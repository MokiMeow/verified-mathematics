$ErrorActionPreference = 'Stop'
Set-Location -LiteralPath $PSScriptRoot
function Read-SanityResult([string] $logPath) {
  $jsonLines = @(Get-Content -LiteralPath $logPath | Where-Object { $_.TrimStart().StartsWith('{') })
  if ($jsonLines.Count -ne 1) { throw "Expected one JSON result in $logPath" }
  return ($jsonLines[0] | ConvertFrom-Json -AsHashtable)
}
$sourceFiles = @(
  'Kantorovich.lean', 'Kantorovich/Stability.lean',
  'Kantorovich/ThreeCertificates.lean', 'Kantorovich/ThreeStability.lean',
  'Kantorovich/Examples.lean'
)
$theoremCount = 0
foreach ($relativePath in $sourceFiles) {
  $source = Get-Content -Raw -LiteralPath $relativePath
  $withoutComments = [regex]::Replace($source, '/-[\s\S]*?-/', '')
  $withoutComments = [regex]::Replace($withoutComments, '--[^\r\n]*', '')
  if ($withoutComments -match '\b(sorry|admit|native_decide|unsafe|axiom)\b') {
    throw "Forbidden proof declaration or placeholder in $relativePath"
  }
  $theoremCount += [regex]::Matches($withoutComments, '(?m)^theorem\s').Count
}
if ($theoremCount -ne 57) { throw "Expected 57 theorems, found $theoremCount" }
$auditText = (Get-Content -Raw evidence/axioms-background.log) +
  (Get-Content -Raw evidence/axioms-stability.log)
$auditMatches = [regex]::Matches($auditText, "'([^']+)' depends on axioms: \[([^\]]*)\]")
if ($auditMatches.Count -ne 57) { throw 'Axiom report does not cover 57 results' }
$allowedAxioms = @('propext', 'Classical.choice', 'Quot.sound')
foreach ($match in $auditMatches) {
  foreach ($axiom in ($match.Groups[2].Value -split ',\s*')) {
    if ($axiom -and $axiom -notin $allowedAxioms) { throw "Unexpected axiom: $axiom" }
  }
}
$moduleNames = @('Kantorovich', 'Kantorovich.Stability',
  'Kantorovich.ThreeCertificates', 'Kantorovich.ThreeStability', 'Kantorovich.Examples')
$kernelText = Get-Content -Raw evidence/kernel-replay.log
foreach ($moduleName in $moduleNames) {
  if ($kernelText -notmatch ('(?m)^replaying ' + [regex]::Escape($moduleName) + '\s*$')) {
    throw "Kernel log omits $moduleName"
  }
}
$mathlibCommit = (git -C .lake/packages/mathlib rev-parse HEAD).Trim()
if ($LASTEXITCODE -ne 0 -or $mathlibCommit -ne '5ed2965256430c3649e86755f9576b54eca72435') {
  throw 'Wrong mathlib revision'
}
$mathlibStatus = git -C .lake/packages/mathlib status --porcelain
if ($LASTEXITCODE -ne 0 -or $mathlibStatus) { throw 'Mathlib source is modified' }
$filesToHash = $sourceFiles + @('Audit.lean', 'StabilityAudit.lean',
  'lakefile.toml', 'lake-manifest.json', 'lean-toolchain',
  'reciprocal-stability.tex', 'paper/reciprocal-stability.pdf',
  'sanity_checks.py', 'stability_sanity.py', 'certificate_counts.py',
  'verify.ps1', 'record_release_evidence.ps1', 'evidence/commands.json',
  'evidence/certificate-counts.json') +
  @(Get-ChildItem evidence -File -Filter '*.log' | ForEach-Object { 'evidence/' + $_.Name })
$hashes = [ordered]@{}
foreach ($relativePath in $filesToHash) {
  $hashes[$relativePath] = (Get-FileHash -LiteralPath $relativePath -Algorithm SHA256).Hash.ToLowerInvariant()
}
$record = [ordered]@{
  recorded_at_utc = [DateTime]::UtcNow.ToString('o')
  lean_version = (lean --version | Out-String).Trim()
  lake_version = (lake --version | Out-String).Trim()
  python_version = (python --version | Out-String).Trim()
  platform = 'Windows x86_64'
  mathlib_commit = $mathlibCommit
  mathlib_source_unmodified = $true
  theorem_count = $theoremCount
  audited_theorem_names = @($auditMatches | ForEach-Object { $_.Groups[1].Value })
  allowed_axioms = $allowedAxioms
  kernel_replayed_modules = $moduleNames
  commands = (Get-Content -Raw evidence/commands.json | ConvertFrom-Json -AsHashtable)
  background_sanity = (Read-SanityResult 'evidence/sanity-background.log')
  stability_sanity = (Read-SanityResult 'evidence/sanity-stability.log')
  sha256 = $hashes
  scope = 'Lean formal statements and saved declarations, relative to imported mathlib and standard axioms; not journal acceptance, novelty certification, or a second independent proof assistant.'
}
$record | ConvertTo-Json -Depth 10 | Set-Content -LiteralPath evidence/verification.json -Encoding utf8
Write-Output 'Recorded 57 audited theorems, five kernel-replayed modules, pinned unmodified mathlib, and artifact hashes.'
