import Mathlib.Tactic

/-!
# Analysis I, Appendix B.1: The decimal representation of natural numbers

Am implementation of the decimal representation of Mathlib's natural numbers {lean}`ℕ`.

This is separate from the way decimal numerals are already represenated in Mathlib via the {name}`OfNat` typeclass.
-/

namespace AppendixB

/- The ten digits, together with the base 10 -/
example : 0 = Nat.zero := rfl
example : 1 = (0:Nat).succ := rfl
example : 2 = (1:Nat).succ := rfl
example : 3 = (2:Nat).succ := rfl
example : 4 = (3:Nat).succ := rfl
example : 5 = (4:Nat).succ := rfl
example : 6 = (5:Nat).succ := rfl
example : 7 = (6:Nat).succ := rfl
example : 8 = (7:Nat).succ := rfl
example : 9 = (8:Nat).succ := rfl
example : 10 = (9:Nat).succ := rfl

/-- Definition B.1.1 -/
def Digit := Fin 10

instance Digit.instZero : Zero Digit := ⟨0, by decide⟩
instance Digit.instOne : One Digit := ⟨1, by decide⟩
instance Digit.instTwo : OfNat Digit 2 := ⟨2, by decide⟩
instance Digit.instThree : OfNat Digit 3 := ⟨3, by decide⟩
instance Digit.instFour : OfNat Digit 4 := ⟨4, by decide⟩
instance Digit.instFive : OfNat Digit 5 := ⟨5, by decide⟩
instance Digit.instSix : OfNat Digit 6 := ⟨6, by decide⟩
instance Digit.instSeven : OfNat Digit 7 := ⟨7, by decide⟩
instance Digit.instEight : OfNat Digit 8 := ⟨8, by decide⟩
instance Digit.instNine : OfNat Digit 9 := ⟨9, by decide⟩

instance Digit.instFintype : Fintype Digit := Fin.fintype 10
instance Digit.instDecidableEq : DecidableEq Digit := instDecidableEqFin 10

instance Digit.instInhabited : Inhabited Digit := ⟨ 0 ⟩

@[coe]
abbrev Digit.toNat (d:Digit) : ℕ := d.val

instance Digit.instCoeNat : Coe Digit Nat where
  coe := toNat

theorem Digit.lt (d:Digit) : (d:ℕ) < 10 := d.isLt

abbrev Digit.mk {n:ℕ} (h: n < 10) : Digit := ⟨n, h⟩

@[simp]
theorem Digit.toNat_mk {n:ℕ} (h: n < 10) : (Digit.mk h:ℕ) = n := rfl

@[simp]
theorem Digit.inj (d d':Digit) : d = d' ↔ (d:ℕ) = d' := by grind

theorem Digit.mk_eq_iff (d:Digit) {n:ℕ} (h: n < 10) : d = mk h ↔ (d:ℕ) = n := by
  convert Digit.inj d (mk h)
#check (0:Digit)
#check (1:Digit)
#check (2:Digit)
#check (3:Digit)
#check (4:Digit)
#check (5:Digit)
#check (6:Digit)
#check (7:Digit)
#check (8:Digit)
#check (9:Digit)

theorem Digit.eq (n: Digit) : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by
  fin_cases n <;> simp +decide

/-- Definition B.1.2 -/
structure PosintDecimal where
  digits : List Digit
  nonempty : digits ≠ []
  nonzero : digits.head nonempty ≠ 0

theorem PosintDecimal.congr' {p q:PosintDecimal} (h: p.digits = q.digits) : p = q := by
  obtain ⟨ pd, _, _ ⟩ := p
  obtain ⟨ qd, _, _ ⟩ := q
  congr

theorem PosintDecimal.congr {p q:PosintDecimal} (h: p.digits.length = q.digits.length)
  (h': ∀ (n:ℕ) (h₁ : n < p.digits.length) (h₂: n < q.digits.length), p.digits.get ⟨ n, h₁ ⟩ = q.digits.get ⟨ n, h₂ ⟩) : p = q := by
  apply congr'
  simp_all [List.ext_get_iff]

abbrev PosintDecimal.head (p:PosintDecimal): Digit := p.digits.head p.nonempty

theorem PosintDecimal.head_ne_zero (p:PosintDecimal) : p.head ≠ 0 := p.nonzero

theorem PosintDecimal.head_ne_zero' (p:PosintDecimal) : (p.head:ℕ) ≠ 0 := by
  by_contra!
  apply head_ne_zero p
  simp_all [Digit.toNat, Digit.inj]; rfl

theorem PosintDecimal.length_pos (p:PosintDecimal) : 0 < p.digits.length := by
  simp [List.length_pos_iff, p.nonempty]

/-- A slightly clunky way of creating decimals. -/
def PosintDecimal.mk' (head:Digit) (tail:List Digit) (h: head ≠ 0) : PosintDecimal := {
  digits := head :: tail
  nonempty := by aesop
  nonzero := h
}

-- the positive integer decimal 314
#check PosintDecimal.mk' 3 [1, 4] (by decide)

-- the positive integer decimal 3
#check PosintDecimal.mk' 3 [] (by decide)

-- the positive integer decimal 10
#check PosintDecimal.mk' 1 [0] (by decide)

/-- We are indexing digits in a decimal from left to right rather than from right to left, thus necessitating a reversal here. -/
@[coe]
def PosintDecimal.toNat (p:PosintDecimal) : Nat :=
  ∑ i:Fin p.digits.length, p.digits[p.digits.length - 1 - ↑i].toNat * 10 ^ (i:ℕ)

instance PosintDecimal.instCoeNat : Coe PosintDecimal Nat where
  coe := toNat

example : (PosintDecimal.mk' 3 [1, 4] (by decide):ℕ) = 314 := by decide

/-- Remark B.1.3 -/
@[simp]
theorem PosintDecimal.ten_eq_ten : (mk' 1 [0] (by decide):ℕ) = 10 := by
  decide

theorem PosintDecimal.digit_eq {d:Digit} (h: d ≠ 0) : (mk' d [] h:ℕ) = d := by
  simp [toNat, mk']

theorem PosintDecimal.pos (p:PosintDecimal) : 0 < (p:ℕ) := by
  simp [toNat]
  calc
    _ < (p.head:ℕ) * 10 ^ (p.digits.length - 1) := by
      have := p.head_ne_zero'
      positivity
    _ ≤ _ := by
      have := p.length_pos
      set a : Fin p.digits.length := ⟨ p.digits.length - 1, by omega ⟩
      convert Finset.single_le_sum _ (Finset.mem_univ a)
      . simp [a, head, List.head_eq_getElem]
      . infer_instance
      grind

/-- An operation implicit in the proof of Theorem B.1.4: -/
abbrev PosintDecimal.append (p:PosintDecimal) (d:Digit) : PosintDecimal :=
  mk' p.head (p.digits.tail ++ [d]) p.head_ne_zero

/-- {name}`toNat` equals Horner (left-fold) evaluation of the digit list. -/
theorem PosintDecimal.toNat_eq_foldl (q : PosintDecimal) :
    q.toNat = q.digits.foldl (fun acc (d : Digit) => acc * 10 + d.toNat) 0 := by
  suffices h : ∀ (L : List Digit) (acc : ℕ),
      L.foldl (fun a (d : Digit) => a * 10 + d.toNat) acc =
      acc * 10 ^ L.length + ∑ i : Fin L.length, (L[L.length - 1 - ↑i]).toNat * 10 ^ (↑i : ℕ)
    from by simp [toNat, h q.digits 0]
  intro L; induction L with
  | nil => simp
  | cons a t ih =>
    intro acc; simp only [List.foldl_cons, List.length_cons]
    -- Decompose the Fin (t.length+1) sum: last term is a*10^|t|, rest matches the Fin t.length sum
    have : ∑ x : Fin (t.length + 1), ((a :: t)[t.length - ↑x] : ℕ) * 10 ^ (↑x : ℕ) =
        (∑ x : Fin t.length, (t[t.length - 1 - ↑x] : ℕ) * 10 ^ (↑x : ℕ)) + a * 10 ^ t.length := by
      refine (Fin.sum_univ_castSucc _).trans ?_
      congr 1 <;> grind
    grind

@[simp]
theorem PosintDecimal.append_toNat (p:PosintDecimal) (d:Digit) :
  (p.append d:ℕ) = d.toNat + 10 * p.toNat  := by
  rw [toNat_eq_foldl, toNat_eq_foldl]; simp only [append, mk']
  rw [show p.head :: (p.digits.tail ++ [d]) = p.digits ++ [d] from by
    simp [head, ← List.cons_append, List.cons_head_tail]]
  rw [List.foldl_append]; simp [List.foldl]; ring

theorem PosintDecimal.eq_append {p:PosintDecimal} (h: 2 ≤ p.digits.length) : ∃ (q:PosintDecimal) (d:Digit), p = q.append d := by
  use mk' p.head (p.digits.tail.dropLast) p.head_ne_zero
  set a := p.digits.getLast p.nonempty; use a
  apply congr'
  simp [mk']
  rw [←p.digits.cons_head_tail p.nonempty]
  congr 1
  convert (List.dropLast_append_getLast _).symm using 2; grind
  simp [←List.length_pos_iff]; omega

/-- Theorem B.1.4 (Uniqueness and existence of decimal representations) -/
theorem PosintDecimal.exists_unique (n:ℕ) : n > 0 → ∃! p:PosintDecimal, (p:ℕ) = n := by
  -- this proof is written to follow the structure of the original text.
  apply n.case_strong_induction_on
  . simp
  -- note: the variable `m` in the text is referred to as `m+1` here.
  clear n; intro m hind _
  obtain hm | hm := lt_or_ge m 9
  . apply ExistsUnique.intro (mk' (.mk (show m+1 < 10 by omega)) [] (by simp [Digit.mk]))
    . simp [mk', Digit.mk, toNat, Digit.toNat]
    intro d hd
    obtain hdl | hdl := lt_or_ge d.digits.length 2
    . replace hdl : d.digits.length = 1 := by linarith [d.length_pos]
      have _subsing : Subsingleton (Fin d.digits.length) := by simp [Fin.subsingleton_iff_le_one, hdl]
      let zero : Fin d.digits.length := ⟨ 0, by omega ⟩
      simp [toNat, hdl, Fintype.sum_subsingleton _ zero, zero, Digit.toNat] at hd
      apply congr
      . simp [hdl, mk']
      intro i hi₁ hi₂
      replace hi₁ : i = 0 := by omega
      simp [hi₁, mk', Digit.mk, hd]
    have : d.toNat ≥ 10 := calc
      _ ≥ (d.head:ℕ) * 10^(d.digits.length-1) := by
        set a : Fin d.digits.length := ⟨ d.digits.length - 1, by omega ⟩
        convert Finset.single_le_sum _ (Finset.mem_univ a)
        . simp [a, head, List.head_eq_getElem]
        . infer_instance
        intros; positivity
      _ ≥ 1 * 10^(2-1) := by
        gcongr
        . have := d.head_ne_zero'; omega
        norm_num
      _ = 10 := by norm_num
    linarith
  have := (m+1).mod_add_div 10
  set s := (m+1)/10
  set r := (m+1) % 10
  have hr : r < 10 := by grind
  specialize hind s _ _ <;> try linarith
  choose b hb huniq using hind; simp at huniq
  apply ExistsUnique.intro (b.append (.mk hr))
  . simp [←this, hb]
  intro a ha
  obtain hal | hal := lt_or_ge a.digits.length 2
  . replace hal : a.digits.length = 1 := by linarith [a.length_pos]
    have _subsing : Subsingleton (Fin a.digits.length) := by simp [Fin.subsingleton_iff_le_one, hal]
    let zero : Fin a.digits.length := ⟨ 0, by linarith ⟩
    simp [toNat, hal, Fintype.sum_subsingleton _ zero, zero, Digit.toNat] at ha
    observe : a.digits[0].val < 10
    linarith
  obtain ⟨ b', b'₀, rfl ⟩ := eq_append hal
  simp [←this] at ha
  observe : (b'₀:ℕ) < 10
  replace : (s:ℤ) = (b':ℕ) := by omega
  have hb'₀r: (b'₀:ℕ) = (r:ℤ) := by omega
  simp at *
  rw [←b'₀.mk_eq_iff hr] at hb'₀r
  rw [huniq b' this.symm, hb'₀r]

@[simp]
theorem PosintDecimal.coe_inj (p q:PosintDecimal) : (p:ℕ) = (q:ℕ) ↔ p = q := by
  constructor <;> intro h
  . exact (exists_unique _ q.pos).unique h rfl
  rw [h]


inductive IntDecimal where
  | zero : IntDecimal
  | pos : PosintDecimal → IntDecimal
  | neg : PosintDecimal → IntDecimal

def IntDecimal.toInt : IntDecimal → Int
  | zero => 0
  | pos p => p.toNat
  | neg p => -p.toNat

instance IntDecimal.instCoeInt : Coe IntDecimal Int where
  coe := toInt

example : (IntDecimal.neg (PosintDecimal.mk' 3 [1, 4] (by decide)):ℤ) = -314 := by decide

theorem IntDecimal.Int_bij : Function.Bijective IntDecimal.toInt := by
  constructor
  . intro p q hpq
    cases p with
    | zero => cases q with
      | zero => rfl
      | pos q => simp [toInt] at hpq; linarith [q.pos]
      | neg q => simp [toInt] at hpq; linarith [q.pos]
    | pos p => cases q with
      | zero => simp [toInt] at hpq; linarith [p.pos]
      | pos q => simpa [toInt] using hpq
      | neg q => simp [toInt] at hpq; linarith [q.pos]
    | neg p => cases q with
      | zero => simp [toInt] at hpq; linarith [p.pos]
      | pos q => simp [toInt] at hpq; linarith [q.pos]
      | neg q => simpa [toInt] using hpq
  intro n
  obtain h | rfl | h := lt_trichotomy n 0
  . generalize e: -n = m
    lift m to Nat using (by omega)
    choose p hp _ using PosintDecimal.exists_unique _ (show 0 < m by omega)
    use neg p
    simp [toInt, hp, ←e]
  . use zero; simp [toInt]
  lift n to Nat using (by omega); simp at h
  choose p hp _ using PosintDecimal.exists_unique _ h
  use pos p
  simp [toInt, hp]

abbrev PosintDecimal.digit (p:PosintDecimal) (i:ℕ) : Digit :=
  if h: i < p.digits.length then p.digits[p.digits.length - i - 1] else 0

abbrev PosintDecimal.carry (p q:PosintDecimal) : ℕ → ℕ := Nat.rec 0 (fun i ε ↦ if ((p.digit i:ℕ) + (q.digit i:ℕ) + ε) < 10 then 0 else 1)

theorem PosintDecimal.carry_zero (p q:PosintDecimal) : p.carry q 0 = 0 := by convert Nat.rec_zero _ _

theorem PosintDecimal.carry_succ (p q:PosintDecimal) (i:ℕ) : p.carry q (i+1) = if ((p.digit i:ℕ) + (q.digit i:ℕ) + p.carry q i < 10) then 0 else 1 :=
  Nat.rec_add_one 0 (fun i ε ↦ if ((p.digit i:ℕ) + (q.digit i:ℕ) + ε) < 10 then 0 else 1) i

abbrev PosintDecimal.sum_digit (p q:PosintDecimal) (i:ℕ) : ℕ :=
  if (p.digit i + q.digit i + (p.carry q) i < 10) then
    p.digit i + q.digit i + (p.carry q) i
  else
    p.digit i + q.digit i + (p.carry q) i - 10

theorem PosintDecimal.digit_le (p: PosintDecimal) (i:ℕ) : (p.digit i:ℕ) < 10 := by
  simp only [Fin.is_lt]

theorem PosintDecimal.carry_le (p q:PosintDecimal) (i:ℕ) : p.carry q i ≤ 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [PosintDecimal.carry]
    simp
    split_ifs
    . exact Nat.zero_le 1
    . norm_num

/-- Exercise B.1.1 -/
theorem PosintDecimal.sum_digit_lt (p q:PosintDecimal) (i:ℕ) :
  p.sum_digit q i < 10 := by
  rw [sum_digit]
  split_ifs
  . linarith
  . have hp : (p.digit i:ℕ) < 10 := PosintDecimal.digit_le p i
    have hq : (q.digit i:ℕ) < 10 := PosintDecimal.digit_le q i
    have hc : (p.carry q i) ≤ 1 := PosintDecimal.carry_le p q i
    simp
    omega

/-- Define this number such that it satisfies the two following theorems. -/
def PosintDecimal.sum_digit_top (p q:PosintDecimal) : ℕ := by
  let m := Nat.max p.digits.length q.digits.length
  if p.carry q m = 1 then
    exact m
  else
    exact m - 1

theorem PosintDecimal.leading_nonzero (p q:PosintDecimal) :
    p.sum_digit q (p.sum_digit_top q) ≠ 0 := by
  rw [PosintDecimal.sum_digit_top]
  split_ifs
  . grind
  . -- the leading digit (at position m-1, where m is the max length) is nonzero
    rename_i hc1
    set m := p.digits.length.max q.digits.length with hm
    have hle1 : p.digits.length ≤ m := by rw [hm]; exact le_max_left _ _
    have hle2 : q.digits.length ≤ m := by rw [hm]; exact le_max_right _ _
    have hor : m = p.digits.length ∨ m = q.digits.length := by rw [hm]; exact max_choice _ _
    have hpos : 1 ≤ m := by have := p.length_pos; omega
    have hc0 : p.carry q m = 0 := by have := p.carry_le q m; omega
    have hcs := p.carry_succ q (m - 1)
    rw [show m - 1 + 1 = m by omega, hc0] at hcs
    have hlt : (p.digit (m-1):ℕ) + (q.digit (m-1):ℕ) + p.carry q (m-1) < 10 := by
      by_contra h
      rw [if_neg h] at hcs
      omega
    rw [sum_digit, if_pos hlt]
    have key : ∀ r : PosintDecimal, r.digits.length = m → (r.digit (m-1):ℕ) ≠ 0 := by
      intro r hr
      have hi : m - 1 < r.digits.length := by omega
      have e : r.digits.length - (m - 1) - 1 = 0 := by omega
      have hd : r.digit (m-1) = r.head := by
        simp only [digit, dif_pos hi, e]
        rw [head, List.head_eq_getElem]
      rw [hd]
      exact r.head_ne_zero'
    by_cases hpm : p.digits.length = m
    · have := key p hpm; omega
    · have := key q (by omega); omega

theorem PosintDecimal.out_of_range_eq_zero (p q:PosintDecimal) :
    ∀ i > ↑(p.sum_digit_top q), p.sum_digit q i = 0 := by
  intro i hi
  rw [sum_digit_top] at hi
  set m := p.digits.length.max q.digits.length with hm
  have hz : ((0:Digit):ℕ) = 0 := rfl
  have hpos : 1 ≤ m := by
    have := p.length_pos
    have : p.digits.length ≤ m := by rw [hm]; exact le_max_left _ _
    omega
  have hdp : ∀ j, m ≤ j → p.digit j = 0 := by
    intro j hj
    have hnlt : ¬ j < p.digits.length := by
      have : p.digits.length ≤ m := by rw [hm]; exact le_max_left _ _
      omega
    simp [digit, hnlt]
  have hdq : ∀ j, m ≤ j → q.digit j = 0 := by
    intro j hj
    have hnlt : ¬ j < q.digits.length := by
      have : q.digits.length ≤ m := by rw [hm]; exact le_max_right _ _
      omega
    simp [digit, hnlt]
  have hcarry : ∀ j, m + 1 ≤ j → p.carry q j = 0 := by
    intro j hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have hck := p.carry_le q k
    rw [carry_succ, hdp k (by omega), hdq k (by omega)]
    simp only [hz]
    rw [if_pos (by omega)]
  have hfin : ∀ j, m ≤ j → p.carry q j = 0 → p.sum_digit q j = 0 := by
    intro j hj hcj
    rw [sum_digit, hdp j hj, hdq j hj, hcj]
    simp only [hz]
    norm_num
  by_cases hc : p.carry q m = 1
  · rw [dif_pos hc] at hi
    exact hfin i (by omega) (hcarry i (by omega))
  · rw [dif_neg hc] at hi
    have him : m ≤ i := by omega
    apply hfin i him
    rcases Nat.eq_or_lt_of_le him with heq | h
    · rw [← heq]; have := p.carry_le q m; omega
    · exact hcarry i (by omega)

def PosintDecimal.longAddition (p q : PosintDecimal) : PosintDecimal where
  digits := List.ofFn (n := p.sum_digit_top q + 1)
              (fun i => Digit.mk (p.sum_digit_lt q (p.sum_digit_top q - i)))
  nonempty := by simp
  nonzero := by
    rw [List.head_eq_getElem, List.getElem_ofFn]
    intro h
    apply p.leading_nonzero q
    simpa [show ((0:Digit):ℕ) = 0 from rfl] using congrArg Digit.toNat h

/-- A decimal's value is the truncated series of its digits, for any cutoff past its length. -/
theorem PosintDecimal.digit_sum (r:PosintDecimal) (N:ℕ) (hN: r.digits.length ≤ N) :
    ∑ k ∈ Finset.range N, ((r.digit k:ℕ)) * 10^k = r.toNat := by
  have hdig : ∀ k (hk : k < r.digits.length),
      (r.digit k:ℕ) = (r.digits[r.digits.length-1-k]'(by omega):ℕ) := by
    intro k hk
    rw [PosintDecimal.digit, dif_pos hk]
    simp only [show r.digits.length - k - 1 = r.digits.length - 1 - k from by omega]
  have key : r.toNat = ∑ k ∈ Finset.range r.digits.length, ((r.digit k:ℕ)) * 10^k := by
    rw [toNat, ← Fin.sum_univ_eq_sum_range (fun k => ((r.digit k:ℕ)) * 10^k) r.digits.length]
    apply Finset.sum_congr rfl
    intro i _
    rw [hdig ↑i i.isLt]
  rw [key]
  symm
  refine Finset.sum_subset (fun x hx => ?_) (fun k _ hk => ?_)
  · rw [Finset.mem_range] at hx ⊢; omega
  · rw [Finset.mem_range, not_lt] at hk
    rw [PosintDecimal.digit, dif_neg (by omega)]
    simp

/-- Each digit of the long-addition result is the corresponding sum digit. -/
theorem PosintDecimal.digit_longAddition (p q:PosintDecimal) (i:ℕ) :
    (((p.longAddition q).digit i):ℕ) = p.sum_digit q i := by
  by_cases hi : i ≤ p.sum_digit_top q
  · have hlt : i < (p.longAddition q).digits.length := by
      simp only [PosintDecimal.longAddition, List.length_ofFn]; omega
    rw [PosintDecimal.digit, dif_pos hlt]
    simp only [PosintDecimal.longAddition, List.length_ofFn, List.getElem_ofFn, Digit.toNat_mk]
    congr 1
    omega
  · push_neg at hi
    have hge : ¬ i < (p.longAddition q).digits.length := by
      simp only [PosintDecimal.longAddition, List.length_ofFn]; omega
    rw [PosintDecimal.digit, dif_neg hge]
    simp only [show ((0:Digit):ℕ) = 0 from rfl]
    exact (p.out_of_range_eq_zero q i (by exact_mod_cast hi)).symm

theorem PosintDecimal.sum_eq (p q:PosintDecimal) (i:ℕ) :
    (((p.longAddition q).digit i):ℕ) = p.sum_digit q i ∧ (p.longAddition q:ℕ) = p + q := by
  refine ⟨p.digit_longAddition q i, ?_⟩
  set m := p.digits.length.max q.digits.length with hm
  -- The carry/sum recurrence at each position.
  have carry_id : ∀ k, (p.digit k:ℕ) + (q.digit k:ℕ) + p.carry q k
      = p.sum_digit q k + 10 * p.carry q (k+1) := by
    intro k
    rw [carry_succ, sum_digit]
    split_ifs <;> omega
  -- Telescoping identity: the partial sum of result digits plus the carry equals the
  -- partial sums of the two addends.
  have tele : ∀ N, (∑ k ∈ Finset.range N, p.sum_digit q k * 10^k) + p.carry q N * 10^N
      = (∑ k ∈ Finset.range N, (p.digit k:ℕ) * 10^k)
        + (∑ k ∈ Finset.range N, (q.digit k:ℕ) * 10^k) := by
    intro N
    induction N with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, pow_succ]
      set Ssd := ∑ k ∈ Finset.range n, p.sum_digit q k * 10^k
      set Sdp := ∑ k ∈ Finset.range n, (p.digit k:ℕ) * 10^k
      set Sdq := ∑ k ∈ Finset.range n, (q.digit k:ℕ) * 10^k
      have hmul : p.sum_digit q n * 10^n + p.carry q (n+1) * (10^n * 10)
          = ((p.digit n:ℕ) + (q.digit n:ℕ) + p.carry q n) * 10^n := by
        rw [carry_id n]; ring
      calc (Ssd + p.sum_digit q n * 10^n) + p.carry q (n+1) * (10^n * 10)
          = Ssd + (p.sum_digit q n * 10^n + p.carry q (n+1) * (10^n * 10)) := by ring
        _ = Ssd + ((p.digit n:ℕ) + (q.digit n:ℕ) + p.carry q n) * 10^n := by rw [hmul]
        _ = (Ssd + p.carry q n * 10^n) + ((p.digit n:ℕ) * 10^n + (q.digit n:ℕ) * 10^n) := by ring
        _ = (Sdp + Sdq) + ((p.digit n:ℕ) * 10^n + (q.digit n:ℕ) * 10^n) := by rw [ih]
        _ = (Sdp + (p.digit n:ℕ) * 10^n) + (Sdq + (q.digit n:ℕ) * 10^n) := by ring
  -- The carry has vanished by position `m+1`, and `longAddition` has no digits past `m`.
  have hdpm : (p.digit m :ℕ) = 0 := by
    have hle : p.digits.length ≤ m := by rw [hm]; exact le_max_left _ _
    rw [PosintDecimal.digit, dif_neg (by omega)]; rfl
  have hdqm : (q.digit m :ℕ) = 0 := by
    have hle : q.digits.length ≤ m := by rw [hm]; exact le_max_right _ _
    rw [PosintDecimal.digit, dif_neg (by omega)]; rfl
  have hcarryN : p.carry q (m+1) = 0 := by
    have hc := p.carry_le q m
    rw [carry_succ, if_pos (by rw [hdpm, hdqm]; omega)]
  have htop : p.sum_digit_top q ≤ m := by rw [PosintDecimal.sum_digit_top]; split_ifs <;> omega
  have hlenLA : (p.longAddition q).digits.length ≤ m + 1 := by
    simp only [PosintDecimal.longAddition, List.length_ofFn]; omega
  have key_la : (p.longAddition q:ℕ) = ∑ k ∈ Finset.range (m+1), p.sum_digit q k * 10^k := by
    rw [← (p.longAddition q).digit_sum (m+1) hlenLA]
    exact Finset.sum_congr rfl (fun k _ => by rw [p.digit_longAddition q k])
  have key_p : (p:ℕ) = ∑ k ∈ Finset.range (m+1), (p.digit k:ℕ) * 10^k :=
    (p.digit_sum (m+1) (by have : p.digits.length ≤ m := by rw [hm]; exact le_max_left _ _
                           omega)).symm
  have key_q : (q:ℕ) = ∑ k ∈ Finset.range (m+1), (q.digit k:ℕ) * 10^k :=
    (q.digit_sum (m+1) (by have : q.digits.length ≤ m := by rw [hm]; exact le_max_right _ _
                           omega)).symm
  have ht := tele (m+1)
  rw [hcarryN] at ht
  simp only [zero_mul, add_zero] at ht
  rw [key_la, ht, ← key_p, ← key_q]
