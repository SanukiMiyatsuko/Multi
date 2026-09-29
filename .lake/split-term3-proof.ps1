$ErrorActionPreference = 'Stop'
$taskRoot = 'F:/projects/leanprojects/wellfound/Multi'
$termPath = Join-Path $taskRoot 'Multi/Term3.lean'
$source = [IO.File]::ReadAllText($termPath).Replace("`r`n", "`n")
$targetStart = $source.IndexOf('theorem T.OT_is_wellfounded')
if ($targetStart -lt 0) { throw 'Target theorem not found.' }
$syntax = $source.Substring(0, $targetStart)
$decStart = $syntax.IndexOf("decreasing_by`n")
$decEnd = $syntax.IndexOf('def T.LF (n : Nat)')
if ($decStart -lt 0 -or $decEnd -le $decStart) { throw 'Termination proof boundaries not found.' }
$proof = @'
decreasing_by
  · exact T.size_lt_size_P_first s0 s1 s2 s3
  · exact T.size_lt_size_P_first s0 s1 s2 s3
  · exact T.size_lt_size_P_second s0 s1 s2 s3
  · exact Nat.lt_trans (T.dom_omega_size s1 l0 l1 _h1).2 (T.size_lt_size_P_second s0 s1 s2 s3)
  · exact T.size_lt_size_P_second s0 s1 s2 s3
  · exact T.size_lt_size_P_second s0 s1 s2 s3
  · exact Nat.lt_trans (T.dom_omega_size s1 l0 l1 _h1).1 (T.size_lt_size_P_second s0 s1 s2 s3)
  · exact T.size_lt_size_P_second s0 s1 s2 s3
  · exact T.size_lt_size_P_second s0 s1 s2 s3
  · exact T.size_lt_size_P_second s0 s1 s2 s3
  · exact T.size_lt_size_P_third s0 s1 s2 s3
  · exact T.size_lt_size_P_third s0 s1 s2 s3
  · exact Nat.lt_trans (T.dom_omega_size s2 l0 l1 _h2).2 (T.size_lt_size_P_third s0 s1 s2 s3)
  · exact T.size_lt_size_P_third s0 s1 s2 s3
  · exact T.size_lt_size_P_third s0 s1 s2 s3
  · exact Nat.lt_trans (T.dom_omega_size s2 l0 l1 _h2).1 (T.size_lt_size_P_third s0 s1 s2 s3)
  · exact T.size_lt_size_P_third s0 s1 s2 s3
  · exact T.size_lt_size_P_third s0 s1 s2 s3
  · exact T.size_lt_size_P_third s0 s1 s2 s3
  · exact T.size_lt_size_P_fourth s0 s1 s2 s3


'@
$syntax = $syntax.Substring(0, $decStart) + $proof.Replace("`r`n", "`n") + $syntax.Substring($decEnd)
[IO.File]::WriteAllText((Join-Path $taskRoot 'Multi/Term3Syntax.lean'), $syntax)
[IO.File]::WriteAllText($termPath, "import Multi.Constructive.Term3Fundamental`n`n" + $source.Substring($targetStart))
