import PEqualNP.Defs.Represents
import Mathlib.Tactic.IntervalCases

namespace PEqualNP.Outside.Scratch19384

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def inputs3 : List Nat := [7, 56, 448, 73, 146, 292]

private def table (m : Nat) (u v : Fin 3) : Bool :=
  m.testBit (3 * u.val + v.val)

-- Each circuit is encoded in base 1024, with its first gate in the lowest
-- digit and its output index in the highest. The certificate checks below
-- validate the codes against the corpus evaluator.
private def upperCodes : Nat → Array Nat
  | 0 => #[
    31, 6147, 6148, 7346484, 6149, 7346485, 7346501, 0,
    6163, 7395585, 8698220803, 10007599911169, 8698221827, 10007599912193, 10007566685443, 7608339,
    6164, 8966393859, 7411969, 10007616687361, 8698221828, 10007566669060, 10007616689409, 7608340,
    7362868, 10007599927553, 10007616703745, 8698253569, 10282176139269, 11673541044869429, 11673541044869445, 8865732916
  ]
  | 1 => #[
    6165, 8966394883, 8966394884, 10007566668037, 7428353, 10007633464577, 10007633465601, 7608341,
    7362869, 10007599928577, 10282176140292, 11673541045918004, 10007633480961, 8698254593, 11673541045918021, 8865732917,
    7362885, 10282176156675, 10007616705793, 11673541062695220, 10007633481985, 11673541062695221, 8698270977, 8865732933,
    1, 7624707, 7624708, 8882493748, 7624709, 8882493749, 8882493765, 6401
  ]
  | 2 => #[
    6179, 7395586, 8698237187, 10007599911170, 8698238211, 10007599912194, 10007583462659, 7608355,
    7395602, 3, 10007566651651, 7657476, 10007566652675, 7657477, 11374748746716419, 6403,
    8698237203, 10007549874451, 10282226418723, 11673592531048706, 11656051921538053, 13089845641633614853, 13090126910414949381, 10179180794131,
    10007599927570, 7657492, 11673592531048722, 8916113665, 13089845692888008709, 10230720386308, 14586053639884875515909, 8866027540
  ]
  | 3 => #[
    8698238227, 10007549875475, 11656051922586628, 13089845641634663428, 10282243195939, 11673609710917890, 13090126927594818564, 10179180795155,
    10007599928594, 7657493, 13089845692889057284, 10230988559364, 11673609710917906, 8916130049, 14586053657477061560324, 8866027541,
    10007583462675, 11374731566847251, 13089845676027956228, 14585747606258605902852, 13089845676027956229, 14585747606258605902853, 11656051956122659, 11550481628599571,
    7624739, 6419, 10196360663299, 8882804740, 10196360664323, 8882804741, 11568073814643971, 7608595
  ]
  | 4 => #[
    6180, 8966410243, 7411970, 10007616687362, 8698238212, 10007583446276, 10007616689410, 7608356,
    8966410259, 10007549858083, 10282226419731, 11673592532097281, 11656326530747397, 13089845641616854021, 13090126910415981573, 10179448967187,
    7411986, 10282226436099, 4, 7673859, 10007566652676, 11374748746700036, 7673861, 6404,
    10007616703762, 11673592548874497, 7673875, 8932874497, 13089845710066829317, 14586053639903129109509, 10247900255491, 8866043923
  ]
  | 5 => #[
    8698238228, 11656051922587651, 10007549875476, 13089845641634664451, 10282243195940, 13090126927594819587, 11673609710934274, 10179180795156,
    10007583446292, 13089845676011180035, 11374731566830868, 14585747606258589126659, 13089845676011180037, 11656051939345444, 14585747606258589126661, 11550481628583188,
    10007616705810, 13089845710068926467, 7673877, 10248168428547, 11673609710934290, 14586053657477078337539, 8932907265, 8866043925,
    7624740, 10196628836355, 6420, 8882821123, 10196360664324, 11568073814627588, 8882821125, 7608596
  ]
  | 6 => #[
    7379252, 10007599943938, 10007616720130, 8698253570, 10282192916485, 11673558224738613, 11673558224738629, 8865749300,
    10007599943954, 7657508, 11673592532097298, 8916113666, 13089845692904785925, 10230720402692, 14586053639885949257733, 8866027556,
    10007616720146, 11673592548874498, 7673891, 8932874498, 13089845710083606533, 14586053639903129110533, 10247900271875, 8866043939,
    8698253586, 8916113682, 8932874514, 6452, 11656051938314245, 11603258169922820, 11620850355967235, 7608628
  ]
  | 7 => #[
    10282192916501, 13090126876108674051, 13090126876108674052, 11656051938297877, 11374731550052645, 14585747606241408226307, 14585747606241408226308, 11550756238053397,
    11673558224754997, 10230720402708, 14586053604755230741508, 11603258153145620, 14586053604755230741509, 11603532846466084, 14641139733022276604163, 11550704765539604,
    11673558224755013, 14586053604755230757891, 10247900271891, 11620850339190035, 14586053604755230757893, 14641139733022276603140, 11621125032510499, 11550721945408787,
    8882526516, 8882804772, 8882821155, 7625012, 11568348424097797, 11568296951584004, 11568314131453187, 8865995060
  ]
  | 8 => #[
    6181, 8966411267, 8966411268, 10007583445253, 7428354, 10007633464578, 10007633465602, 7608357,
    8966411283, 10007549859107, 11656326531795972, 13089845641617902596, 10282243196947, 11673609711966465, 13090126927595850756, 10179448968211,
    8966411284, 11656326531796995, 10007549859108, 13089845641617903619, 10282243196948, 13090126927595851779, 11673609711982849, 10179448968212,
    10007583445269, 13089845676010132483, 13089845676010132484, 11656051938296869, 11374731566829845, 14585747606258588079107, 14585747606258588079108, 11550481628582165
  ]
  | 9 => #[
    7428370, 10282243213315, 10282243213316, 11374748746699013, 5, 7690243, 7690244, 6405,
    10007633480978, 11673609728743681, 13089845727246698500, 14586053657495315153924, 7690259, 8949651713, 10265080123651, 8866060307,
    10007633482002, 13089845727247747075, 11673609728760065, 14586053657495331931139, 7690260, 10265348296707, 8949668097, 8866060308,
    7624741, 10196628837379, 10196628837380, 11568073814626565, 6421, 8882837507, 8882837508, 7608597
  ]
  | 10 => #[
    7379253, 10007599944962, 10282192917508, 11673558225787188, 10007633497346, 8698254594, 11673558225787205, 8865749301,
    10007599944978, 7657509, 13089845692905834500, 10230988575748, 11673609711966482, 8916130050, 14586053657478135302148, 8866027557,
    10282192917524, 13090126876109721603, 11374731550053668, 14585747606241409273859, 13090126876109721605, 11656051939346452, 14585747606241409273861, 11550756238054420,
    11673558225803572, 10230988575764, 14586053604756304482308, 11603258153129252, 14586053604756304482309, 11603532846467092, 14641139733022275556611, 11550705033712660
  ]
  | 11 => #[
    10007633497362, 11673609728743682, 13089845727263475716, 14586053657495315154948, 7690275, 8949651714, 10265080140035, 8866060323,
    8698254610, 8916130066, 11656051939362820, 11603532846483460, 8949651730, 6453, 11638442542010627, 7608629,
    11673558225803589, 14586053604756304499715, 14586053604756304499716, 14641139733022275554565, 10265080140051, 11638442525233427, 11638717201777699, 11550739125276947,
    8882526517, 8882804773, 11568348424098820, 11568297219757060, 8882837539, 7625013, 11568331311321347, 8865995061
  ]
  | 12 => #[
    7379269, 10282192933891, 10007616722178, 11673558242564404, 10007633498370, 11673558242564405, 8698270978, 8865749317,
    10282192933907, 11374731550070051, 13090126876126497796, 14585747606241426050052, 13090126876126497797, 14585747606241426050053, 11656051956123667, 11550756238070803,
    10007616722194, 13089845710085703683, 7673893, 10248168444931, 11673609711982866, 14586053657478152079363, 8932907266, 8866043941,
    11673558242580788, 14586053604773484351491, 10248168444947, 11620850339173667, 14586053604773484351493, 14641139733022274508036, 11621125032511507, 11550722213581843
  ]
  | 13 => #[
    10007633498386, 13089845727264524291, 11673609728760066, 14586053657495331932163, 7690276, 10265348313091, 8949668098, 8866060324,
    11673558242580789, 14586053604773484352515, 14586053604773484352516, 14641139733022274507013, 10265348313107, 11638442525217059, 11638717201778707, 11550739393450003,
    8698270994, 11656051956140035, 8932907282, 11621125032527875, 8949668114, 11638717201795075, 6469, 7608645,
    8882526533, 11568348424115203, 8882821157, 11568314399626243, 8882837540, 11568331579494403, 7625029, 8865995077
  ]
  | 14 => #[
    2, 7641091, 7641092, 8899270964, 7641093, 8899270965, 8899270981, 6402,
    7641107, 6435, 10213540516099, 8899581956, 10213540517123, 8899581957, 11585665983911171, 7608611,
    7641108, 10213808689155, 6436, 8899598339, 10213540517124, 11585665983894788, 8899598341, 7608612,
    8899287348, 8899581972, 8899598355, 7641396, 11585940593364997, 11585889137612036, 11585906317481219, 8866011444
  ]
  | 15 => #[
    7641109, 10213808690179, 10213808690180, 11585665983893765, 6437, 8899614723, 8899614724, 7608613,
    8899287349, 8899581973, 11585940593366020, 11585889405785092, 8899614739, 7641397, 11585923497349379, 8866011445,
    8899287365, 11585940593382403, 8899598357, 11585906585654275, 8899614740, 11585923765522435, 7641413, 8866011461,
    6418, 7624995, 7624996, 8882788660, 7624997, 8882788661, 8882788677, 7702785
  ]
  | _ => #[]

private def goodMasks : Nat → Nat
  | 0 => 0xffc1a180898080e9c1d50040004000c1a100b320000020a18040201100000010890000008f08088980400000080500048000200008000302e9c1a110890402e9
  | 1 => 0xffe9e991e98583ffe9d58051804500d5e980b331800023b3915131f1000000f1e98080008f0d0b8f854500000dcd00cd830023000b00ababffd5b3f18fcdabff
  | 2 => 0xfffffff9ffedebfffffde1d5c9d580fdffe1fbb3a980b3fbf9d5b3f1804020f1ffc9a980ef8f8fefedd580408fcd08cdeb80b3208f08ababfffdfbf1efcdabff
  | 3 => 0xfffffffffffffffffffff9f5edddc3fffff9fff3eba5bbfffff5f3ff99d5b3ffffedeb99ffcfafffffdda5d5cfff8fffffc3bbb3af8fffffffffffffffffffff
  | 4 => 0xfffffffffffffffffffffffdfffdebfffffffffbffedfbfffffdfbfff9d5b3fffffffff9ffefeffffffdedd5efff8fffffebfbb3ef8fffffffffffffffffffff
  | _ => 0

private def decodeGate (d : Nat) : Gate :=
  ⟨if d < 256 then .and else .or, [d / 16 % 16, d % 16]⟩

private def decode (fuel code : Nat) : Circuit :=
  match fuel with
  | 0 => ⟨[], code⟩
  | fuel + 1 =>
    if code < 32 then ⟨[], code⟩
    else
      let rest := decode fuel (code / 1024)
      ⟨decodeGate (code % 1024) :: rest.gates, rest.output⟩

private def witness (m : Nat) : Circuit :=
  decode 8 ((upperCodes (m / 32))[m % 32]?.getD 31)

private theorem mono_of_exact (C : Circuit) (h : TopForm.IsAO2 6 C) : Monotone2 C := by
  intro g hg
  exact ⟨by simpa using h.1 g hg, (h.2.2 g hg).le⟩

set_option maxHeartbeats 0 in
private theorem goodWitnessBlock (b : Fin 16) :
    ∀ (i : Fin 32) (s : Fin 5),
      (goodMasks s.val).testBit (32 * b.val + i.val) = true →
        (witness (511 ^^^ (32 * b.val + i.val))).size ≤ s.val + 2 := by
  have h := b.isLt
  interval_cases b.val <;> decide +kernel

private theorem goodWitness (s : Fin 5) (m : Fin 512) :
    (goodMasks s.val).testBit m.val = true →
      (witness (511 ^^^ m.val)).size ≤ s.val + 2 := by
  have h := goodWitnessBlock ⟨m.val / 32, by omega⟩
    ⟨m.val % 32, Nat.mod_lt _ (by decide)⟩ s
  simpa only [Nat.div_add_mod] using h

private theorem inputs_eval (u v : Fin 3) :
    inputs3.map (fun m => table m u v) = oneEach u v := by
  revert u v
  decide +kernel

private theorem full_eval (u v : Fin 3) : table 511 u v = true := by
  revert u v
  decide +kernel

private theorem table_complement (m : Nat) (u v : Fin 3) :
    table (511 ^^^ m) u v = !table m u v := by
  simp only [table, Nat.testBit_xor]
  rw [show (511 : Nat).testBit (3 * u.val + v.val) = true from full_eval u v]
  cases m.testBit (3 * u.val + v.val) <;> rfl

private def choices (w : List Nat) : List Nat :=
  w.flatMap fun a => w.flatMap fun b => [a &&& b, a ||| b]

private def fresh (w : List Nat) : List Nat :=
  ((choices w).filter fun a => !w.contains a).eraseDups

private def pairGood (good : Nat → Bool) (a : Nat) (w : List Nat) : Bool :=
  w.all fun b => good (a &&& b) && good (a ||| b)

private def closedFor (good : Nat → Bool) (w : List Nat) : Prop :=
  ∀ a ∈ w, ∀ b ∈ w, good (a &&& b) = true ∧ good (a ||| b) = true

private def explores (good : Nat → Bool) : Nat → List Nat → Bool
  | 0, _ => true
  | 1, _ => true
  | k + 2, w => (fresh w).all (fun a => pairGood good a w && explores good (k + 1) (a :: w))

private theorem mem_choices {w : List Nat} {a b : Nat} (ha : a ∈ w) (hb : b ∈ w) :
    a &&& b ∈ choices w ∧ a ||| b ∈ choices w := by
  constructor <;> exact List.mem_flatMap.mpr ⟨a, ha, List.mem_flatMap.mpr ⟨b, hb, by simp⟩⟩

private theorem choices_good {good : Nat → Bool} {w : List Nat}
    (hc : closedFor good w) {a : Nat} (ha : a ∈ choices w) : good a = true := by
  obtain ⟨b, hb, hc'⟩ := List.mem_flatMap.mp ha
  obtain ⟨c, hc'', he⟩ := List.mem_flatMap.mp hc'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · exact he ▸ (hc b hb c hc'').1
  · exact he ▸ (hc b hb c hc'').2

private theorem closedFor_cons {good : Nat → Bool} {w : List Nat} {a : Nat}
    (h : closedFor good w) (ha : good a = true) (hpair : pairGood good a w = true) :
    closedFor good (a :: w) := by
  intro b hb c hc
  have hp (k : Nat) (hk : k ∈ w) := Bool.and_eq_true_iff.mp (List.all_eq_true.mp hpair k hk)
  simp only [List.mem_cons] at hb hc
  rcases hb with rfl | hb <;> rcases hc with rfl | hc
  · simp [ha]
  · exact hp _ hc
  · simpa [Nat.land_comm, Nat.lor_comm] using hp _ hb
  · exact h _ hb _ hc

private theorem explores_extend {good : Nat → Bool} {k : Nat} {w : List Nat} {a : Nat}
    (he : explores good (k + 1) w = true) (hc : 0 < k + 1 → closedFor good w)
    (ha : a ∈ choices w) (hn : a ∉ w) :
    good a = true ∧ (0 < k → closedFor good (a :: w)) ∧ explores good k (a :: w) = true := by
  have hgood := choices_good (hc (by omega)) ha
  refine ⟨hgood, ?_, ?_⟩
  · intro hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have hmem : a ∈ fresh w := by simp [fresh, ha, hn]
    have h := Bool.and_eq_true_iff.mp (List.all_eq_true.mp he a hmem)
    exact closedFor_cons (hc (by omega)) hgood h.1
  · cases k with
    | zero => rfl
    | succ j =>
      have hmem : a ∈ fresh w := by simp [fresh, ha, hn]
      exact (Bool.and_eq_true_iff.mp (List.all_eq_true.mp he a hmem)).2

private def seed : List Nat := 0 :: 511 :: inputs3

private theorem seed_good (s : Fin 5) (hs : 0 < s.val) :
    seed.all ((goodMasks s.val).testBit) = true := by
  revert s
  decide +kernel

private theorem zero_good :
    (0 :: inputs3).all ((goodMasks 0).testBit) = true := by decide +kernel

private theorem seed_closed (s : Fin 5) (hs : 0 < s.val) :
    closedFor ((goodMasks s.val).testBit) seed := by
  have h : ∀ s : Fin 5, 0 < s.val →
      (choices seed).all ((goodMasks s.val).testBit) = true := by decide +kernel
  intro a ha b hb
  have hm := mem_choices ha hb
  exact ⟨List.all_eq_true.mp (h s hs) _ hm.1, List.all_eq_true.mp (h s hs) _ hm.2⟩

private theorem seed_search_one : explores ((goodMasks 1).testBit) 1 seed = true := rfl

private theorem seed_search_two : explores ((goodMasks 2).testBit) 2 seed = true := by
  decide +kernel

private theorem seed_search_three : explores ((goodMasks 3).testBit) 3 seed = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem seed_search_four : explores ((goodMasks 4).testBit) 4 seed = true := by
  simp only [explores, List.all_eq_true]
  change ∀ a ∈ [63, 455, 1, 79, 2, 151, 4, 295, 504, 8, 121, 16, 186, 32, 316, 64, 457, 128, 466, 256, 484, 219, 365, 438], _
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private theorem seed_search (s : Fin 5) (hs : 0 < s.val) :
    explores ((goodMasks s.val).testBit) s.val seed = true := by
  have h := s.isLt
  interval_cases s.val
  · exact seed_search_one
  · exact seed_search_two
  · exact seed_search_three
  · exact seed_search_four

private def wireRead (w : List Nat) (i : Nat) : Nat := w.getD i 0

private theorem wireRead_mem {w available : List Nat} (h : ∀ a ∈ w, a ∈ available)
    (hzero : 0 ∈ available) (i : Nat) : wireRead w i ∈ available := by
  unfold wireRead
  rw [List.getD_eq_getElem?_getD]
  cases hi : w[i]? with
  | none => exact hzero
  | some a => exact h a (List.mem_of_getElem? hi)

private def gateMask (w : List Nat) (g : Gate) : Nat :=
  match g.inputs with
  | [] => if (match g.op with | .and => true | _ => false) then 511 else 0
  | [i] => wireRead w i
  | i :: j :: _ =>
    match g.op with
    | .and => wireRead w i &&& wireRead w j
    | .or => wireRead w i ||| wireRead w j
    | _ => 0

private theorem gateMask_mem {w available : List Nat}
    (hw : ∀ a ∈ w, a ∈ available) (hzero : 0 ∈ available) (hfull : 511 ∈ available)
    (g : Gate) :
    gateMask w g ∈ available ∨ gateMask w g ∈ choices available := by
  cases g with
  | mk op pins =>
    cases pins with
    | nil => left; simp only [gateMask]; split <;> assumption
    | cons i tail =>
      cases tail with
      | nil => exact Or.inl (wireRead_mem hw hzero i)
      | cons j tail =>
        have h := mem_choices (wireRead_mem hw hzero i) (wireRead_mem hw hzero j)
        cases op <;> first | exact Or.inr h.1 | exact Or.inr h.2 | exact Or.inl hzero

private theorem gateMask_eval (w : List Nat) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (u v : Fin 3) :
    table (gateMask w g) u v =
      g.op.eval (g.inputs.map fun i => (w.map fun m => table m u v).getD i false) := by
  have read (i : Nat) :
      (w.map fun m => table m u v).getD i false = table (wireRead w i) u v := by
    simpa [wireRead, table] using
      (List.getD_map (l := w) (d := 0) (n := i) (fun m => table m u v))
  cases g with
  | mk op pins =>
    have hp : pins.length ≤ 2 := hg.2
    cases op <;> try simp at hg
    all_goals
      cases pins with
      | nil => first | exact full_eval u v | simp [gateMask, GateOp.eval, table]
      | cons i tail =>
        cases tail with
        | nil =>
          simp only [List.map_cons, List.map_nil, read, gateMask]
          cases table (wireRead w i) u v <;> rfl
        | cons j tail =>
          have ht : tail = [] := by
            simp only [List.length_cons] at hp
            exact List.length_eq_zero_iff.mp (by omega)
          subst tail
          simp only [List.map_cons, List.map_nil, read]
          simp [gateMask, GateOp.eval, table]

private def runMasks (gs : List Gate) (w : List Nat) : List Nat :=
  gs.foldl (fun w g => w ++ [gateMask w g]) w

private theorem run_eval (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (w : List Nat) (u v : Fin 3) :
    (runMasks gs w).map (fun m => table m u v) =
      gs.foldl (fun x g => x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])
        (w.map fun m => table m u v) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [runMasks, List.foldl_cons]
    change (runMasks gs (w ++ [gateMask w g])).map _ = _
    rw [ih (fun a ha => hg a (by simp [ha])), List.map_append, List.map_singleton,
      gateMask_eval w g (hg g (by simp)) u v]

private theorem circuit_mask (C : Circuit) (hC : Monotone2 C) (u v : Fin 3) :
    C.eval (oneEach u v) = table (wireRead (runMasks C.gates inputs3) C.output) u v := by
  have h := run_eval C.gates hC inputs3 u v
  rw [inputs_eval] at h
  unfold Circuit.eval Circuit.wires
  rw [← h]
  simpa [wireRead, table] using
    (List.getD_map (l := runMasks C.gates inputs3) (d := 0) (n := C.output)
      (fun m => table m u v))

private def witnessOK (m : Nat) : Prop :=
  let C := witness m
  TopForm.IsAO2 6 C ∧ C.size ≤ 7 ∧ wireRead (runMasks C.gates inputs3) C.output = m

private instance (m : Nat) : Decidable (witnessOK m) := by
  unfold witnessOK
  infer_instance

set_option maxHeartbeats 0 in
private theorem checkedWitnessBlock (b : Fin 16) :
    ∀ i : Fin 32, witnessOK (32 * b.val + i.val) := by
  have h := b.isLt
  interval_cases b.val <;> decide +kernel

private theorem checkedWitness (m : Fin 512) :
    let C := witness m.val
    TopForm.IsAO2 6 C ∧ C.size ≤ 7 ∧ Represents (table m.val) C := by
  have h := checkedWitnessBlock ⟨m.val / 32, by omega⟩
    ⟨m.val % 32, Nat.mod_lt _ (by decide)⟩
  have hm : witnessOK m.val := by simpa only [Nat.div_add_mod] using h
  obtain ⟨hmono, hsize, hmask⟩ := hm
  refine ⟨hmono, hsize, fun u v => ?_⟩
  rw [circuit_mask _ (mono_of_exact _ hmono), hmask]

private theorem run_good (good : Nat → Bool) (gs : List Gate) (fuel : Nat)
    (w available : List Nat) (hlen : gs.length ≤ fuel)
    (hw : ∀ a ∈ w, a ∈ available) (hzero : 0 ∈ available) (hfull : 511 ∈ available)
    (hg : available.all good = true) (hc : 0 < fuel → closedFor good available)
    (he : explores good fuel available = true) (i : Nat) :
    good (wireRead (runMasks gs w) i) = true := by
  induction gs generalizing fuel w available with
  | nil => exact List.all_eq_true.mp hg _ (wireRead_mem hw hzero i)
  | cons g gs ih =>
    change good (wireRead (runMasks gs (w ++ [gateMask w g])) i) = true
    cases fuel with
    | zero => simp at hlen
    | succ k =>
      by_cases h : gateMask w g ∈ available
      · exact ih (k + 1) _ available (by simp at hlen; omega)
          (by simp only [List.mem_append, List.mem_singleton]; aesop)
          hzero hfull hg hc he
      · have hm := (gateMask_mem hw hzero hfull g).resolve_left h
        obtain ⟨hgood, hclosed, hnext⟩ := explores_extend he hc hm h
        exact ih k _ (gateMask w g :: available) (by simpa using hlen)
          (by simp only [List.mem_append, List.mem_cons]; aesop)
          (by simp [hzero]) (by simp [hfull]) (by simp [hgood, hg]) hclosed hnext

private theorem code_lt (m : Nat) : m % 512 < 512 := Nat.mod_lt _ (by decide)

private theorem table_mod (m : Nat) (u v : Fin 3) :
    table (m % 512) u v = table m u v := by
  unfold table
  have h : 3 * u.val + v.val < 9 := by omega
  simpa using (Nat.testBit_mod_two_pow m 9 (3 * u.val + v.val)).trans
    (by simp [h])

private def pack : List Bool → Nat
  | [] => 0
  | b :: bs => b.toNat ||| (pack bs <<< 1)

private theorem pack_bit (bs : List Bool) (i : Nat) :
    (pack bs).testBit i = bs.getD i false := by
  induction bs generalizing i with
  | nil => simp [pack]
  | cons b bs ih =>
    cases i with
    | zero => cases b <;> simp [pack]
    | succ i =>
      have h : (1 : Nat).testBit (i + 1) = false := by simp [Nat.testBit_succ]
      cases b <;> simp [pack, Nat.testBit_shiftLeft, ih, List.getD, h]

private theorem exists_code (A : Fin 3 → Fin 3 → Bool) :
    ∃ m : Fin 512, A = table m.val := by
  let row (i : Fin 9) : Fin 3 := ⟨i.val / 3, by omega⟩
  let col (i : Fin 9) : Fin 3 := ⟨i.val % 3, by omega⟩
  let bs := List.ofFn (fun i : Fin 9 => A (row i) (col i))
  refine ⟨⟨pack bs % 512, code_lt _⟩, ?_⟩
  funext u v
  rw [table_mod]
  unfold table
  rw [pack_bit]
  have hi : 3 * u.val + v.val < 9 := by omega
  simp only [bs, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, dite_true, Option.getD_some]
  congr 1 <;> apply Fin.ext <;> simp only [row, col] <;> omega

set_option exponentiation.threshold 512 in
theorem complement_exact_upper_three {s : Nat} (A : Fin 3 → Fin 3 → Bool)
    (h : RepSizeAtMost (fun u v => !A u v) s) :
    RepSize2AtMost A (s + 2) := by
  by_cases hs : 5 ≤ s
  · obtain ⟨m, rfl⟩ := exists_code A
    obtain ⟨hm, hz, hr⟩ := checkedWitness m
    exact ⟨witness m.val, hm, by omega, hr⟩
  · obtain ⟨C, hC, hsize, hr⟩ := h
    let raw := wireRead (runMasks C.gates inputs3) C.output
    let m : Fin 512 := ⟨raw % 512, code_lt _⟩
    have rawGood : (goodMasks s).testBit raw = true := by
      by_cases hzero : s = 0
      · subst s
        have hg : C.gates = [] := List.length_eq_zero_iff.mp (by simpa [Circuit.size] using hsize)
        have hm : raw ∈ 0 :: inputs3 := by
          simpa [raw, hg, runMasks] using wireRead_mem
            (w := inputs3) (available := 0 :: inputs3)
            (fun a ha => by simp [ha]) (by simp) C.output
        exact List.all_eq_true.mp zero_good _ hm
      · exact run_good _ C.gates s inputs3 seed hsize
          (fun a ha => by simp [seed, ha]) (by simp [seed]) (by simp [seed])
          (seed_good ⟨s, by omega⟩ (by simpa using Nat.pos_of_ne_zero hzero))
          (seed_closed ⟨s, by omega⟩)
          (seed_search ⟨s, by omega⟩ (by simpa using Nat.pos_of_ne_zero hzero)) C.output
    have hraw : raw < 512 := by
      by_contra hn
      have small : goodMasks s < 2 ^ 512 := by
        have : ∀ q : Fin 5, goodMasks q.val < 2 ^ 512 := by decide +kernel
        exact this ⟨s, by omega⟩
      have hz := Nat.testBit_lt_two_pow
        (small.trans_le (Nat.pow_le_pow_right (by decide) (show 512 ≤ raw by omega)))
      rw [hz] at rawGood
      contradiction
    have hm : m.val = raw := Nat.mod_eq_of_lt hraw
    have hbudget := goodWitness ⟨s, by omega⟩ m (by rw [hm]; exact rawGood)
    let c : Fin 512 := ⟨511 ^^^ m.val, by
      have h511 : (511 : Nat) < 2 ^ 9 := by decide
      exact Nat.xor_lt_two_pow h511 m.isLt⟩
    obtain ⟨hmono, _, hrep⟩ := checkedWitness c
    refine ⟨witness c.val, hmono, hbudget, ?_⟩
    intro u v
    rw [hrep u v]
    change table (511 ^^^ m.val) u v = A u v
    rw [table_complement, hm, ← circuit_mask C hC u v, hr u v]
    simp

theorem complement_sizeAtMost_three {s : Nat} (A : Fin 3 → Fin 3 → Bool)
    (h : RepSizeAtMost (fun u v => !A u v) s) :
    RepSizeAtMost A (s + 2) := by
  obtain ⟨C, hm, hsize, hrep⟩ := complement_exact_upper_three A h
  exact ⟨C, mono_of_exact C hm, hsize, hrep⟩

theorem complement_size2AtMost_three {s : Nat} (A : Fin 3 → Fin 3 → Bool)
    (h : RepSize2AtMost (fun u v => !A u v) s) :
    RepSize2AtMost A (s + 2) := by
  obtain ⟨C, hm, hs, hr⟩ := h
  exact complement_exact_upper_three A ⟨C, mono_of_exact C hm, hs, hr⟩

-- The unrestricted reading of the title leaves this range open.
theorem complement_sizeAtMost_ge_four {n s : Nat} (hn : 4 ≤ n) (A : Fin n → Fin n → Bool)
    (h : RepSizeAtMost (fun u v => !A u v) s) :
    RepSizeAtMost A (s + (2 * n - 4)) := by
  sorry

theorem complement_sizeAtMost {n s : Nat} (hn : 3 ≤ n) (A : Fin n → Fin n → Bool)
    (h : RepSizeAtMost (fun u v => !A u v) s) :
    RepSizeAtMost A (s + (2 * n - 4)) := by
  by_cases h3 : n = 3
  · subst n
    exact complement_sizeAtMost_three A h
  · exact complement_sizeAtMost_ge_four (by omega) A h

private theorem budget_iff_repSize {n : Nat} (A : Fin n → Fin n → Bool) (s : Nat) :
    RepSizeAtMost A s ↔ repSize A ≤ (s : ℕ∞) := by
  constructor
  · intro h
    exact sInf_le ⟨s, rfl, h⟩
  · intro h
    let S : Set ℕ∞ := {r | ∃ k : Nat, r = (k : ℕ∞) ∧ RepSizeAtMost A k}
    have hS : S.Nonempty := by
      by_contra hEmpty
      have he : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hEmpty
      change sInf S ≤ (s : ℕ∞) at h
      simp [he] at h
    obtain ⟨k, hk, C, hm, hsz, hr⟩ := csInf_mem hS
    change repSize A = (k : ℕ∞) at hk
    rw [hk] at h
    exact ⟨C, hm, hsz.trans (ENat.natCast_le_natCast.mp h), hr⟩

theorem repSize_complement_iff {n : Nat} (A : Fin n → Fin n → Bool) (d : Nat) :
    (repSize A ≤ repSize (fun u v => !A u v) + (d : ℕ∞)) ↔
      ∀ s : Nat, RepSizeAtMost (fun u v => !A u v) s → RepSizeAtMost A (s + d) := by
  constructor
  · intro h s hs
    apply (budget_iff_repSize A (s + d)).mpr
    rw [ENat.natCast_add]
    exact h.trans (add_le_add_left ((budget_iff_repSize _ s).mp hs) _)
  · intro h
    unfold repSize
    rw [ENat.sInf_add]
    refine le_iInf fun b => le_iInf fun hb => ?_
    obtain ⟨k, rfl, hk⟩ := hb
    rw [← ENat.natCast_add]
    exact (budget_iff_repSize A _).mp (h k hk)

theorem complement_repSize_three (A : Fin 3 → Fin 3 → Bool) :
    repSize A ≤ repSize (fun u v => !A u v) + 2 :=
  (repSize_complement_iff A 2).mpr (fun _ => complement_sizeAtMost_three A)

theorem complement_repSize {n : Nat} (hn : 3 ≤ n) (A : Fin n → Fin n → Bool) :
    repSize A ≤ repSize (fun u v => !A u v) + ((2 * n - 4 : Nat) : ℕ∞) :=
  (repSize_complement_iff A _).mpr (fun _ => complement_sizeAtMost hn A)

theorem complement_repSize2_three (A : Fin 3 → Fin 3 → Bool) :
    repSize2 A ≤ repSize2 (fun u v => !A u v) + 2 := by
  unfold repSize2
  rw [ENat.sInf_add]
  refine le_iInf fun b => le_iInf fun hb => ?_
  obtain ⟨k, rfl, hk⟩ := hb
  have h := complement_size2AtMost_three A hk
  simpa [ENat.natCast_add] using
    (sInf_le (show ∃ l : Nat, ((k + 2 : Nat) : ℕ∞) = (l : ℕ∞) ∧ RepSize2AtMost A l
      from ⟨k + 2, rfl, h⟩))

end PEqualNP.Outside.Scratch19384

#print axioms PEqualNP.Outside.Scratch19384.complement_sizeAtMost_three
#print axioms PEqualNP.Outside.Scratch19384.complement_repSize_three
#print axioms PEqualNP.Outside.Scratch19384.complement_size2AtMost_three
#print axioms PEqualNP.Outside.Scratch19384.complement_repSize2_three
#print axioms PEqualNP.Outside.Scratch19384.complement_sizeAtMost
#print axioms PEqualNP.Outside.Scratch19384.complement_repSize
