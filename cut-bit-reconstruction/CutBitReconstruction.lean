import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring

/-!
# Reconstructing the second bit of a graph cut

A graph is given by a list of edges whose endpoints are natural-number labels.
Repeated edges are counted with multiplicity. Loops contribute zero.
The result applies to any finite graph after choosing an ordering of its vertices.
-/

namespace CutBit

open scoped BigOperators

abbrev Bit := ZMod 2

def vertex (v : ℕ) (s : Finset ℕ) : Bit := if v ∈ s then 1 else 0

def mixedDifference (f : Finset ℕ → Bit) (a b : ℕ) : Bit :=
  f (Finset.Ico a (b + 1)) - f (Finset.Ico (a + 1) (b + 1)) -
    f (Finset.Ico a b) + f (Finset.Ico (a + 1) b)

def Reconstructed (f : Finset ℕ → Bit) : Prop :=
  ∀ s, f s = ∑ a ∈ s, ∑ b ∈ s, mixedDifference f a b

private theorem mixedDifference_add (f g : Finset ℕ → Bit) (a b : ℕ) :
    mixedDifference (fun s => f s + g s) a b =
      mixedDifference f a b + mixedDifference g a b := by
  unfold mixedDifference
  ring

private theorem reconstructed_add {f g : Finset ℕ → Bit}
    (hf : Reconstructed f) (hg : Reconstructed g) :
    Reconstructed (fun s => f s + g s) := by
  intro s
  simp only [mixedDifference_add, Finset.sum_add_distrib, ← hf s, ← hg s]

private theorem interval_product (u v a b : ℕ) :
    vertex u (Finset.Ico a b) * vertex v (Finset.Ico a b) =
      (if a ≤ min u v then (1 : Bit) else 0) *
        (if max u v < b then (1 : Bit) else 0) := by
  simp only [vertex, Finset.mem_Ico, le_min_iff, max_lt_iff]
  split_ifs <;> first | rfl | omega

private theorem product_difference (u v a b : ℕ) :
    mixedDifference (fun s => vertex u s * vertex v s) a b =
      if a = min u v ∧ b = max u v then 1 else 0 := by
  let l (i : ℕ) : Bit := if i ≤ min u v then 1 else 0
  let r (j : ℕ) : Bit := if max u v < j then 1 else 0
  have hl : l a - l (a + 1) = if a = min u v then 1 else 0 := by
    unfold l
    split_ifs <;> first | omega | simp
  have hr : r (b + 1) - r b = if b = max u v then 1 else 0 := by
    unfold r
    split_ifs <;> first | omega | simp
  unfold mixedDifference
  simp only [interval_product]
  change l a * r (b + 1) - l (a + 1) * r (b + 1) -
    l a * r b + l (a + 1) * r b = _
  calc
    _ = (l a - l (a + 1)) * (r (b + 1) - r b) := by ring
    _ = _ := by rw [hl, hr]; split_ifs <;> simp_all

private theorem reconstructed_product (u v : ℕ) :
    Reconstructed (fun s => vertex u s * vertex v s) := by
  intro s
  simp only [product_difference, ite_and]
  by_cases huv : u ≤ v
  · by_cases hu : u ∈ s <;> simp [min_eq_left huv, max_eq_right huv, vertex, hu]
  · have hvu : v ≤ u := by omega
    simp [min_eq_right hvu, max_eq_left hvu, vertex, mul_comm]

private inductive Linear : (Finset ℕ → Bit) → Prop where
  | zero : Linear (fun _ => 0)
  | var (v : ℕ) : Linear (vertex v)
  | add {f g} : Linear f → Linear g → Linear (fun s => f s + g s)

private theorem reconstructed_zero : Reconstructed (fun _ => 0) := by
  simp [Reconstructed, mixedDifference]

private theorem reconstructed_vertex_mul (u : ℕ) {g} (hg : Linear g) :
    Reconstructed (fun s => vertex u s * g s) := by
  induction hg with
  | zero => simpa only [mul_zero] using reconstructed_zero
  | var v => exact reconstructed_product u v
  | add _ _ h₁ h₂ => simpa only [mul_add] using reconstructed_add h₁ h₂

private theorem reconstructed_mul {f g} (hf : Linear f) (hg : Linear g) :
    Reconstructed (fun s => f s * g s) := by
  induction hf with
  | zero => simpa only [zero_mul] using reconstructed_zero
  | var u => exact reconstructed_vertex_mul u hg
  | add _ _ h₁ h₂ => simpa only [add_mul] using reconstructed_add h₁ h₂

def crossing (e : ℕ × ℕ) (s : Finset ℕ) : ℕ :=
  if (e.1 ∈ s ↔ e.2 ∈ s) then 0 else 1

def cutSize (s : Finset ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 0
  | e :: es => crossing e s + cutSize s es

def secondBit (n : ℕ) : Bit := (n / 2 : ℕ)

private theorem secondBit_add (m n : ℕ) :
    secondBit (m + n) = secondBit m + secondBit n + (m : Bit) * (n : Bit) := by
  have hc : (m + n) / 2 = m / 2 + n / 2 + (m % 2) * (n % 2) := by
    have hm : m % 2 = 0 ∨ m % 2 = 1 := by omega
    have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases hm with hm | hm <;> rcases hn with hn | hn <;>
      rw [hm, hn] <;> simp <;> omega
  simp only [secondBit, hc, Nat.cast_add, Nat.cast_mul, ZMod.natCast_mod]

private theorem linear_crossing (e : ℕ × ℕ) :
    Linear (fun s => (crossing e s : Bit)) := by
  convert Linear.add (Linear.var e.1) (Linear.var e.2) using 1
  funext s
  by_cases h₁ : e.1 ∈ s <;> by_cases h₂ : e.2 ∈ s <;> simp [crossing, vertex, h₁, h₂]
  decide

private theorem linear_cutSize (edges : List (ℕ × ℕ)) :
    Linear (fun s => (cutSize s edges : Bit)) := by
  induction edges with
  | nil => simpa only [cutSize, Nat.cast_zero] using Linear.zero
  | cons e es ih =>
    simpa only [cutSize, Nat.cast_add] using Linear.add (linear_crossing e) ih

def cutBit (edges : List (ℕ × ℕ)) (s : Finset ℕ) : Bit :=
  secondBit (cutSize s edges)

/-- The bit from the cut of any vertex set is recovered from interval cuts. -/
theorem reconstruct_cutBit (edges : List (ℕ × ℕ)) : Reconstructed (cutBit edges) := by
  induction edges with
  | nil =>
    change Reconstructed (fun s => secondBit (cutSize s []))
    simpa [secondBit, cutSize] using reconstructed_zero
  | cons e es ih =>
    have hz (s : Finset ℕ) : secondBit (crossing e s) = 0 := by
      unfold crossing
      split_ifs <;> rfl
    change Reconstructed (fun s => secondBit (cutSize s (e :: es)))
    simpa only [cutBit, cutSize, secondBit_add, hz, zero_add] using
      reconstructed_add ih (reconstructed_mul (linear_crossing e) (linear_cutSize es))

/-- Agreement on every interval implies agreement on every vertex set. -/
theorem cutBit_eq_of_intervals (g h : List (ℕ × ℕ))
    (agree : ∀ a b, cutBit g (Finset.Ico a b) = cutBit h (Finset.Ico a b))
    (s : Finset ℕ) : cutBit g s = cutBit h s := by
  rw [reconstruct_cutBit g s, reconstruct_cutBit h s]
  simp only [mixedDifference, agree]

def thirdCutBit (edges : List (ℕ × ℕ)) (s : Finset ℕ) : Bit :=
  (cutSize s edges / 4 : ℕ)

private def square : List (ℕ × ℕ) := [(0, 1), (1, 2), (2, 3), (3, 0)]

/-- A square and an edgeless graph agree at the third bit on every interval,
but differ on the cut through alternate vertices. -/
theorem thirdCutBit_not_determined :
    (∀ a b, thirdCutBit square (Finset.Ico a b) = thirdCutBit [] (Finset.Ico a b)) ∧
      thirdCutBit square {0, 2} ≠ thirdCutBit [] {0, 2} := by
  constructor
  · intro a b
    by_cases h₀ : a ≤ 0 ∧ 0 < b <;> by_cases h₁ : a ≤ 1 ∧ 1 < b <;>
      by_cases h₂ : a ≤ 2 ∧ 2 < b <;> by_cases h₃ : a ≤ 3 ∧ 3 < b <;>
      first | omega | (simp only [thirdCutBit, square, cutSize, crossing, Finset.mem_Ico,
        h₀, h₁, h₂, h₃]; decide)
  · decide

end CutBit

#print axioms CutBit.reconstruct_cutBit
#print axioms CutBit.cutBit_eq_of_intervals
#print axioms CutBit.thirdCutBit_not_determined
