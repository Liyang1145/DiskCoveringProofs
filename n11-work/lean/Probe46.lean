import N11Formalization.SourceLoop

open N11Formalization

namespace ProbeTest

example (p q : Point) :
    Real.sqrt ((proj p fidx0 - proj q fidx0) * (proj p fidx0 - proj q fidx0)
      + (proj p fidx1 - proj q fidx1) * (proj p fidx1 - proj q fidx1)) = dist p q := by
  rw [dist_point_eq_sqrt]
  simp only [proj, fidx0, fidx1, Fin.eta]
  congr 1
  ring

example (p q : Point) :
    Real.sqrt ((proj p fidx0 - proj q fidx0) * (proj p fidx0 - proj q fidx0)
      + (proj p fidx1 - proj q fidx1) * (proj p fidx1 - proj q fidx1)) = dist p q := by
  rw [dist_point_eq_sqrt]
  simp only [proj, fidx0, fidx1]
  ring_nf

end ProbeTest
