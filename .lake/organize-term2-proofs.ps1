$ErrorActionPreference = 'Stop'
$taskRoot = 'F:/projects/leanprojects/wellfound/Multi'
$termPath = Join-Path $taskRoot 'Multi/term2.lean'
$source = [IO.File]::ReadAllText($termPath).Replace("`r`n", "`n")
$genericStart = $source.IndexOf('theorem T.OT_characterization_of_wellFounded_and_fundamental_properties')
$specialStart = $source.IndexOf('theorem T.OT_characterization_of_fundamental_properties')
$nfGenericComment = $source.IndexOf('/-- A constructive proof of well-foundedness suffices for the characterization. -/')
$nfSpecialStart = $source.IndexOf('theorem T.OT_is_NF (s : T)')
$otStart = $source.IndexOf('def T.OT :=')
$otGenericStart = $source.IndexOf('theorem T.OT_wellFounded_of_NF_wellFounded')
$otSpecialStart = $source.IndexOf('theorem T.OT_is_wellfounded')
if ($genericStart -lt 0 -or $specialStart -le $genericStart -or $nfGenericComment -le $specialStart -or
    $nfSpecialStart -le $nfGenericComment -or $otStart -le $nfSpecialStart -or
    $otGenericStart -le $otStart -or $otSpecialStart -le $otGenericStart) {
  throw 'Expected declaration boundaries were not found.'
}
$common = "import Multi.Term2Syntax`n`n" +
  $source.Substring($otStart, $otGenericStart - $otStart) +
  $source.Substring($genericStart, $specialStart - $genericStart) +
  $source.Substring($nfGenericComment, $nfSpecialStart - $nfGenericComment) +
  $source.Substring($otGenericStart, $otSpecialStart - $otGenericStart)
[IO.File]::WriteAllText((Join-Path $taskRoot 'Multi/Term2Consequences.lean'), $common)
$special = $source.Substring($specialStart, $nfGenericComment - $specialStart)
$constructivePath = Join-Path $taskRoot 'Multi/Constructive/Term2.lean'
$constructive = [IO.File]::ReadAllText($constructivePath).Replace("`r`n", "`n")
$constructive = $constructive.Replace('-- SHARED_API_CHARACTERIZATION', $special.TrimEnd())
[IO.File]::WriteAllText($constructivePath, $constructive)
[IO.File]::WriteAllText($termPath, "import Multi.Constructive.Term2`n`n#print axioms T.OT_is_wellfounded`n")
