$ErrorActionPreference = 'Stop'
$taskRoot = 'F:/projects/leanprojects/wellfound/Multi'
$termPath = Join-Path $taskRoot 'Multi/term2.lean'
$source = [IO.File]::ReadAllText($termPath).Replace("`r`n", "`n")
[IO.File]::WriteAllText((Join-Path $taskRoot '.lake/term2-before-constructive-integration.lean'), $source)
$classStart = $source.IndexOf("namespace T`n`nopen OCF`n")
$classEnd = $source.IndexOf('def T.NF :=')
$wfStart = $source.IndexOf('theorem T.NF_is_wellfounded')
$wfEnd = $source.IndexOf('def T.LF (n : Nat)')
$corollariesStart = $source.IndexOf('theorem T.OT_characterization_of_wellFounded_and_fundamental_properties')
if ($classStart -lt 0 -or $classEnd -le $classStart -or $wfStart -le $classEnd -or $wfEnd -le $wfStart -or $corollariesStart -le $wfEnd) {
  throw 'Expected source boundaries were not found.'
}
$syntax = $source.Substring(0, $classStart).Replace("import Multi.OCF.Hierarchy`n", '') +
  $source.Substring($classEnd, $wfStart - $classEnd) +
  $source.Substring($wfEnd, $corollariesStart - $wfEnd)
$main = "import Multi.Constructive.Term2Closure`n`n" +
  "/-- The order on normal forms is accessible by constructive relative reductions. -/`n" +
  "theorem T.NF_is_wellfounded : WellFounded fun x y : T.NF => x.1 < y.1 :=`n" +
  "  T.Constructive.normalForms_wellFounded`n`n" + $source.Substring($corollariesStart)
$interpretation = "import Multi.Term2Syntax`nimport Multi.OCF.Hierarchy`n`n" +
  "/- Optional classical interpretation, independent of the constructive proof in Multi.term2. -/`n" +
  $source.Substring($classStart, $classEnd - $classStart)
[IO.File]::WriteAllText((Join-Path $taskRoot 'Multi/Term2Syntax.lean'), $syntax)
[IO.File]::WriteAllText((Join-Path $taskRoot 'Multi/OCF/Term2Interpretation.lean'), $interpretation)
$stagePath = Join-Path $taskRoot 'Multi/Constructive/Term2Stages.lean'
$stageSource = [IO.File]::ReadAllText($stagePath).Replace('import Multi.term2', 'import Multi.Term2Syntax')
[IO.File]::WriteAllText($stagePath, $stageSource)
[IO.File]::WriteAllText($termPath, $main)
