import SparseLowerTail.Section08.CertificateSigns
import SparseLowerTail.Section02.Patterns

/-! Analytic tail reduction for the family certificate. Compact-domain
positivity remains explicit; the unbounded-coordinate estimates are proved. -/
noncomputable section
open Set Filter
open scoped Topology
namespace SparseLowerTail.Certificate
open Section04

/-- Logarithmic location of the within-block contact. -/
def qA (z : ℝ) : ℝ := -Real.log (branchA z)

theorem qA_eq {z : ℝ} (hz : 0<z) (hz1 : z<1) :
    qA z=branchLog z*(1+z^2)/(1-z)^2 := by
  rw [qA,branch_logA hz hz1]
  unfold logA
  ring

theorem hasDerivAt_branchLog_tail {z : ℝ} (hz : z≠0) :
    HasDerivAt branchLog (-z⁻¹) z := by
  have he : branchLog=(fun t : ℝ => -Real.log t) := funext branchLog_eq_neg_log
  rw [he]
  exact (Real.hasDerivAt_log hz).neg

theorem branchLog_sq_mul_bound {z : ℝ} (hz : 0<z) (hz40 : z≤1/40) :
    z*(branchLog z)^2≤(369/100:ℝ)^2/40 := by
  let f := fun t : ℝ => t*(branchLog t)^2
  have hd (t : ℝ) (ht : 0<t) : HasDerivAt f ((branchLog t)^2-2*branchLog t) t := by
    convert (hasDerivAt_id t).mul ((hasDerivAt_branchLog_tail ht.ne').pow 2) using 1
    simp only [id_eq,Pi.pow_apply]
    field_simp
    ring
  have hmono : MonotoneOn f (Ioc (0:ℝ) (1/40)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioc _ _)
    · intro t ht
      exact (hd t ht.1).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ioc] at ht
      exact (hd t ht.1).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ioc] at ht
      rw [(hd t ht.1).deriv]
      have hL := branchLog_lower ht.1 ht.2.le
      nlinarith
  have hh := hmono ⟨hz,hz40⟩ (show (1/40:ℝ)∈Ioc (0:ℝ) (1/40) by norm_num) hz40
  have he : branchLog (1/40:ℝ)=Real.log 40 := by norm_num [branchLog]
  dsimp [f] at hh
  rw [he] at hh
  have hlo := log_forty_bounds.1
  have hhi := log_forty_bounds.2
  nlinarith

def tailN (z L : ℝ) : ℝ :=
  2*L^2*z^3+3*L^2*z^2-L^2*z+L*z^4+L*z^2-2*L*z-z^4+2*z^3-2*z+1

def tailT (z L : ℝ) : ℝ :=
  2*L^2*z^5+2*L^2*z^4+6*L^2*z^3-2*L^2*z^2+
  L*z^6+7*L*z^5-19*L*z^4+34*L*z^3-33*L*z^2+7*L*z+3*L+
  3*z^6-13*z^5+24*z^4-14*z^3-17*z^2+27*z-10

theorem tailN_pos {z : ℝ} (hz : 0<z) (hz40 : z≤1/40) :
    0<tailN z (branchLog z) := by
  let L := branchLog z
  have hL : 0≤L := le_trans (by norm_num) (branchLog_lower hz hz40).le
  have hLz := branchLog_mul_bounds hz hz40
  have hL2z := branchLog_sq_mul_bound hz hz40
  have hz4 := pow_le_pow_left₀ hz.le hz40 4
  have hdrop : 1-L^2*z-2*L*z-z^4-2*z≤tailN z L := by
    have hid : tailN z L-(1-L^2*z-2*L*z-z^4-2*z)=
        2*L^2*z^3+3*L^2*z^2+L*z^4+L*z^2+2*z^3 := by unfold tailN; ring
    have hn : 0≤2*L^2*z^3+3*L^2*z^2+L*z^4+L*z^2+2*z^3 := by positivity
    linarith
  change 0≤L*z ∧ L*z≤_ at hLz
  change z*L^2≤_ at hL2z
  nlinarith

theorem tailT_pos {z : ℝ} (hz : 0<z) (hz40 : z≤1/40) :
    0<tailT z (branchLog z) := by
  let L := branchLog z
  have hL : (368/100:ℝ)<L := branchLog_lower hz hz40
  have hL0 : 0≤L := by linarith
  have hLz : 0≤L*z ∧ L*z≤(369/4000:ℝ) := branchLog_mul_bounds hz hz40
  have hz2 := pow_le_pow_left₀ hz.le hz40 2
  have hz3 := pow_le_pow_left₀ hz.le hz40 3
  have hz5 := pow_le_pow_left₀ hz.le hz40 5
  have hp2 := pow_le_pow_left₀ hLz.1 hLz.2 2
  have hp3 := mul_le_mul hLz.2 hz3 (pow_nonneg hz.le 3) (by norm_num : (0:ℝ)≤369/4000)
  have hp1 := mul_le_mul hLz.2 hz40 hz.le (by norm_num : (0:ℝ)≤369/4000)
  have hdrop : 3*L-10-2*(L*z)^2-19*(L*z)*z^3-33*(L*z)*z-
      13*z^5-14*z^3-17*z^2≤tailT z L := by
    have hid : tailT z L-(3*L-10-2*(L*z)^2-19*(L*z)*z^3-33*(L*z)*z-
        13*z^5-14*z^3-17*z^2)=
        2*L^2*z^5+2*L^2*z^4+6*L^2*z^3+L*z^6+7*L*z^5+34*L*z^3+7*L*z+
        3*z^6+24*z^4+27*z := by unfold tailT; ring
    have hn : 0≤2*L^2*z^5+2*L^2*z^4+6*L^2*z^3+L*z^6+7*L*z^5+34*L*z^3+7*L*z+
        3*z^6+24*z^4+27*z := by positivity
    linarith
  nlinarith only [hdrop,hL,hp2,hp3,hp1,hz2,hz3,hz5]

set_option maxHeartbeats 2000000 in
/-- The first exact rational identity in the tail argument. -/
theorem tailN_identity (z L : ℝ) (hz : 1-z≠0) (hp : z+1≠0)
    (hL : L≠0) (hg : gamma z L≠0) :
    multiplier z L*d4 z L*(L*(1+z^2)/(1-z)^2+1)-1=
      -2*tailN z L/((z+1)*gamma z L) := by
  unfold multiplier d4 tailN
  field_simp
  unfold gamma
  ring

set_option maxHeartbeats 2000000 in
/-- The second exact rational identity in the tail argument. -/
theorem tailT_identity (z L : ℝ) (hz : 1-z≠0) (hp : z+1≠0)
    (hL : L≠0) (hg : gamma z L≠0) :
    4*(-d3 z L)-z*(d1 z L+d4 z L*(L*(1+z^2)/(1-z)^2)*(L*(1+z^2)/(1-z)^2+2))=
      -z*tailT z L/(2*(z+1)*gamma z L) := by
  unfold d1 d3 d4 tailT
  field_simp
  ring

/-- The contact log is L plus a positive correction. -/
theorem qA_eq_add {z : ℝ} (hz : 0<z) (hz1 : z<1) :
    qA z=branchLog z+2*branchLog z*z/(1-z)^2 := by
  rw [qA_eq hz hz1]
  have hd : 1-z≠0 := (sub_pos.mpr hz1).ne'
  field_simp
  ring

theorem qA_lower {z : ℝ} (hz : 0<z) (hz40 : z≤1/40) : (368/100:ℝ)<qA z := by
  have hL := branchLog_lower hz hz40
  rw [qA_eq_add hz (by linarith)]
  have hp : 0≤2*branchLog z*z/(1-z)^2 := by positivity
  linarith

theorem tail_threshold_product {z : ℝ} (hz : 0<z) (hz40 : z≤1/40) :
    1<branchMu z*c4 z*(qA z+1) := by
  have hz1 : z<1 := by linarith
  have hL : 0<branchLog z := lt_trans (by norm_num) (branchLog_lower hz hz40)
  have hg := gamma_branch_neg hz hz40
  have hi := tailN_identity z (branchLog z) (sub_pos.mpr hz1).ne'
    (show z+1≠0 by positivity) hL.ne' hg.ne
  have hpos : 0< -2*tailN z (branchLog z)/((z+1)*gamma z (branchLog z)) :=
    div_pos_of_neg_of_neg (mul_neg_of_neg_of_pos (by norm_num) (tailN_pos hz hz40))
      (mul_neg_of_pos_of_neg (by positivity) hg)
  have hscale : branchMu z*c4 z=multiplier z (branchLog z)*d4 z (branchLog z) := by
    unfold c4
    rw [← mul_assoc,branchMu_scaled]
  rw [hscale,qA_eq hz hz1]
  linarith

theorem tail_normalized_gap {z : ℝ} (hz : 0<z) (hz40 : z≤1/40) :
    z*(d1 z (branchLog z)+d4 z (branchLog z)*qA z*(qA z+2))<4*(-d3 z (branchLog z)) := by
  have hz1 : z<1 := by linarith
  have hL : 0<branchLog z := lt_trans (by norm_num) (branchLog_lower hz hz40)
  have hg := gamma_branch_neg hz hz40
  have hi := tailT_identity z (branchLog z) (sub_pos.mpr hz1).ne'
    (show z+1≠0 by positivity) hL.ne' hg.ne
  have hpos : 0< -z*tailT z (branchLog z)/(2*(z+1)*gamma z (branchLog z)) :=
    div_pos_of_neg_of_neg (mul_neg_of_neg_of_pos (neg_neg_of_pos hz) (tailT_pos hz hz40))
      (mul_neg_of_pos_of_neg (by positivity) hg)
  rw [qA_eq hz hz1]
  linarith

/-- A very coarse, kernel-checked exponential bound suffices for the tail. -/
theorem four_mul_exp_neg_two_lt_one : 4*Real.exp (-2:ℝ)<1 := by
  have he1 : 2<Real.exp (1:ℝ) := by
    have hh := Real.add_one_lt_exp (by norm_num : (1:ℝ)≠0)
    linarith
  have he2 : 4<Real.exp (2:ℝ) := by
    rw [show (2:ℝ)=1+1 by norm_num,Real.exp_add]
    nlinarith
  have hp : Real.exp (-2:ℝ)*Real.exp 2=1 := by rw [← Real.exp_add]; norm_num
  have hh := mul_lt_mul_of_pos_left he2 (Real.exp_pos (-2:ℝ))
  nlinarith

def tailGamma (z q : ℝ) : ℝ := Real.exp (-q)*(c1 z+c4 z*(q^2-2*q))

theorem tailGamma_at_contact {z : ℝ} (hz : 0<z) :
    tailGamma z (qA z+2)=Real.exp (-2)*branchB z^3*
      (z*(d1 z (branchLog z)+d4 z (branchLog z)*qA z*(qA z+2))) := by
  have he : Real.exp (-(qA z+2))=Real.exp (-2)*branchA z := by
    rw [show -(qA z+2)= -2+Real.log (branchA z) by unfold qA; ring,Real.exp_add,
      Real.exp_log (branchA_pos hz)]
  unfold tailGamma
  rw [he]
  unfold c1 c4 branchA
  ring

theorem tailGamma_contact_lt {z : ℝ} (hz : 0<z) (hz40 : z≤1/40) :
    tailGamma z (qA z+2)< -c3 z := by
  have hg := tail_normalized_gap hz hz40
  have hd3 := (normalized_coefficient_signs hz hz40).2.2.1
  have hb3 : 0<branchB z^3 := pow_pos (branchB_pos z) 3
  have he := mul_lt_mul_of_pos_left hg (mul_pos (Real.exp_pos (-2)) hb3)
  rw [← tailGamma_at_contact hz] at he
  have hc := mul_lt_mul_of_pos_right four_mul_exp_neg_two_lt_one
    (mul_pos hb3 (neg_pos.mpr hd3))
  unfold c3
  nlinarith

theorem hasDerivAt_tailGamma (z q : ℝ) :
    HasDerivAt (tailGamma z) (-Real.exp (-q)*(c1 z+c4 z*(q^2-4*q+2))) q := by
  convert ((hasDerivAt_neg q).exp).mul
    (((hasDerivAt_id q).pow 2).sub ((hasDerivAt_id q).const_mul 2) |>.const_mul (c4 z) |>.const_add (c1 z)) using 1
  simp only [id_eq,Pi.pow_apply,Pi.sub_apply]
  ring

theorem tailGamma_antitone {z : ℝ} (hz : 0<z) (hz40 : z≤1/40) :
    AntitoneOn (tailGamma z) (Ici (4:ℝ)) := by
  obtain ⟨hc1,_,_,hc4⟩ := coefficient_signs hz hz40
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · intro q _
    exact (hasDerivAt_tailGamma z q).continuousAt.continuousWithinAt
  · intro q _
    exact (hasDerivAt_tailGamma z q).differentiableAt.differentiableWithinAt
  · intro q hq
    rw [interior_Ici] at hq
    rw [(hasDerivAt_tailGamma z q).deriv]
    have hq' : 4<q := hq
    have hp : 0≤q^2-4*q+2 := by nlinarith
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.exp_pos _).le)
      (add_nonneg hc1.le (mul_nonneg hc4.le hp))

theorem tailGamma_lt_neg_c3 {z q : ℝ} (hz : 0<z) (hz40 : z≤1/40)
    (hq : qA z+2≤q) : tailGamma z q< -c3 z := by
  have hqa := qA_lower hz hz40
  have h4 : 4≤qA z+2 := by linarith
  exact ((tailGamma_antitone hz hz40) h4 (h4.trans hq) hq).trans_lt (tailGamma_contact_lt hz hz40)

/-- The original certificate in logarithmic coordinates. -/
def phi (z u v w : ℝ) : ℝ := psi z (Real.exp (-u)) (Real.exp (-v)) (Real.exp (-w))

def logPotential (z q : ℝ) : ℝ :=
  c0 z+c1 z*Real.exp (-q)-c2 z*q*Real.exp (-q)-c3 z*q+c4 z*q^2*Real.exp (-q)

theorem phi_formula (z u v w : ℝ) :
    phi z u v w=logPotential z u+logPotential z v+logPotential z w+
      branchMu z*c3 z*(Real.exp (-u)*Real.exp (-v)+Real.exp (-v)*Real.exp (-w)+Real.exp (-w)*Real.exp (-u))+
      Real.exp (-u)*Real.exp (-v)*Real.exp (-w)*(1-branchMu z*c4 z*(u+v+w)) := by
  unfold phi psi potential logPotential
  simp only [Real.log_exp]
  ring

theorem phi_swap_uv (z u v w : ℝ) : phi z u v w=phi z v u w := psi_swap_xy _ _ _ _
theorem phi_swap_uw (z u v w : ℝ) : phi z u v w=phi z w v u := psi_swap_xw _ _ _ _

theorem hasDerivAt_logPotential (z q : ℝ) :
    HasDerivAt (logPotential z)
      (-c3 z+Real.exp (-q)*(-c1 z+c2 z*(q-1)+c4 z*(2*q-q^2))) q := by
  have he := (hasDerivAt_neg q).exp
  have h := ((((he.const_mul (c1 z)).const_add (c0 z)).sub
    (((hasDerivAt_id q).const_mul (c2 z)).mul he)).sub
    ((hasDerivAt_id q).const_mul (c3 z))).add
    ((((hasDerivAt_id q).pow 2).const_mul (c4 z)).mul he)
  convert h using 1
  simp only [id_eq,Pi.pow_apply]
  ring

def phiDerivative (z u v w : ℝ) : ℝ :=
  -c3 z+Real.exp (-u)*(-c1 z+c2 z*(u-1)+c4 z*(2*u-u^2))-
  branchMu z*c3 z*Real.exp (-u)*(Real.exp (-v)+Real.exp (-w))+
  Real.exp (-u)*Real.exp (-v)*Real.exp (-w)*(branchMu z*c4 z*(u+v+w)-1-branchMu z*c4 z)

theorem hasDerivAt_phi_first (z u v w : ℝ) :
    HasDerivAt (fun t => phi z t v w) (phiDerivative z u v w) u := by
  have he := (hasDerivAt_neg u).exp
  have hsum := ((hasDerivAt_id u).add_const v).add_const w
  have hp := (((he.mul_const (Real.exp (-v))).add_const (Real.exp (-v)*Real.exp (-w))).add
    (he.const_mul (Real.exp (-w)))).const_mul (branchMu z*c3 z)
  have ht := ((he.mul_const (Real.exp (-v))).mul_const (Real.exp (-w))).mul
    ((hsum.const_mul (branchMu z*c4 z)).const_sub 1)
  have h := ((((hasDerivAt_logPotential z u).add_const (logPotential z v)).add_const
    (logPotential z w)).add hp).add ht
  have hfun : (fun t => phi z t v w)=(fun t => logPotential z t+logPotential z v+logPotential z w+
      branchMu z*c3 z*(Real.exp (-t)*Real.exp (-v)+Real.exp (-v)*Real.exp (-w)+Real.exp (-w)*Real.exp (-t))+
      Real.exp (-t)*Real.exp (-v)*Real.exp (-w)*(1-branchMu z*c4 z*(t+v+w))) :=
    funext fun t => phi_formula z t v w
  rw [hfun]
  convert h using 1
  unfold phiDerivative
  simp only [id_eq]
  ring

/-- Actual `lem:certtail`, for the first coordinate. Symmetry gives the other two. -/
theorem phiDerivative_pos {z u v w : ℝ} (hz : 0<z) (hz40 : z≤1/40)
    (hu : qA z+2≤u) (hv : 0≤v) (hw : 0≤w) : 0<phiDerivative z u v w := by
  obtain ⟨hc1,hc2,hc3,hc4⟩ := coefficient_signs hz hz40
  have hμ := branchMu_pos hz (by linarith : z<1)
  have hA : 0<branchMu z*c4 z := mul_pos hμ hc4
  have hqa := qA_lower hz hz40
  have hu1 : 0≤u-1 := by linarith
  have hthreshold := tail_threshold_product hz hz40
  have hslack : 0≤branchMu z*c4 z*(u+v+w)-1-branchMu z*c4 z := by
    have hm := mul_le_mul_of_nonneg_left (show qA z+2≤u+v+w by linarith) hA.le
    nlinarith
  have hp2 : 0≤Real.exp (-u)*c2 z*(u-1) := by positivity
  have hpc : 0≤ -(branchMu z*c3 z*Real.exp (-u)*(Real.exp (-v)+Real.exp (-w))) := by
    have hh : branchMu z*c3 z*Real.exp (-u)*(Real.exp (-v)+Real.exp (-w))≤0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hμ.le hc3.le) (Real.exp_pos _).le)
        (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    linarith
  have hlast : 0≤Real.exp (-u)*Real.exp (-v)*Real.exp (-w)*
      (branchMu z*c4 z*(u+v+w)-1-branchMu z*c4 z) :=
    mul_nonneg (by positivity) hslack
  have hg := tailGamma_lt_neg_c3 hz hz40 hu
  have hid : phiDerivative z u v w=
      -c3 z-tailGamma z u+Real.exp (-u)*c2 z*(u-1)-
      branchMu z*c3 z*Real.exp (-u)*(Real.exp (-v)+Real.exp (-w))+
      Real.exp (-u)*Real.exp (-v)*Real.exp (-w)*(branchMu z*c4 z*(u+v+w)-1-branchMu z*c4 z) := by
    unfold phiDerivative tailGamma
    ring
  rw [hid]
  linarith

theorem deriv_phi_first_pos {z u v w : ℝ} (hz : 0<z) (hz40 : z≤1/40)
    (hu : qA z+2≤u) (hv : 0≤v) (hw : 0≤w) :
    0<deriv (fun t => phi z t v w) u := by
  rw [(hasDerivAt_phi_first z u v w).deriv]
  exact phiDerivative_pos hz hz40 hu hv hw

theorem phi_strictMonoOn_tail {z v w : ℝ} (hz : 0<z) (hz40 : z≤1/40)
    (hv : 0≤v) (hw : 0≤w) : StrictMonoOn (fun u => phi z u v w) (Ici (qA z+2)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · intro u _
    exact (hasDerivAt_phi_first z u v w).continuousAt.continuousWithinAt
  · intro u hu
    rw [interior_Ici] at hu
    exact deriv_phi_first_pos hz hz40 (show qA z+2<u from hu).le hv hw

/-- The tail threshold lies below 12 throughout the compact family range.
The coarser bound 2Lz/(1-z)^2<1/2 is already sufficient. -/
theorem qA_add_two_lt_twelve {z : ℝ} (hz : 0<z) (hz40 : z≤1/40)
    (hL : branchLog z≤19/2) : qA z+2<12 := by
  have hz1 : z<1 := by linarith
  have hd : 0<(1-z)^2 := pow_pos (sub_pos.mpr hz1) 2
  have hdlo : (39/40:ℝ)^2≤(1-z)^2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
  have hLz := (branchLog_mul_bounds hz hz40).2
  have hf : 2*branchLog z*z/(1-z)^2<(1/2:ℝ) := by
    apply (div_lt_iff₀ hd).mpr
    nlinarith
  rw [qA_eq_add hz hz1]
  linarith

/-- Clipping one logarithmic coordinate to 12 strictly improves the certificate
unless that coordinate was already in the compact domain. -/
theorem phi_clip_first {z u v w : ℝ} (hz : 0<z) (hz40 : z≤1/40)
    (hL : branchLog z≤19/2) (hv : 0≤v) (hw : 0≤w) :
    phi z (min u 12) v w≤phi z u v w ∧
      (phi z (min u 12) v w=phi z u v w ↔ u≤12) := by
  by_cases hu : u≤12
  · simp only [min_eq_left hu,le_refl,true_iff]
    exact ⟨trivial,hu⟩
  · have h12 : 12<u := lt_of_not_ge hu
    have hq12 := qA_add_two_lt_twelve hz hz40 hL
    have hh := (phi_strictMonoOn_tail hz hz40 hv hw) hq12.le (hq12.trans h12).le h12
    rw [min_eq_right h12.le]
    exact ⟨hh.le,iff_of_false hh.ne hu⟩

/-- The complete clipping reduction, including strictness outside the box. -/
theorem phi_clip {z u v w : ℝ} (hz : 0<z) (hz40 : z≤1/40)
    (hL : branchLog z≤19/2) (hu : 0≤u) (hv : 0≤v) (hw : 0≤w) :
    phi z (min u 12) (min v 12) (min w 12)≤phi z u v w ∧
      (phi z (min u 12) (min v 12) (min w 12)=phi z u v w ↔
        u≤12 ∧ v≤12 ∧ w≤12) := by
  have hu' : 0≤min u 12 := le_min hu (by norm_num)
  have hv' : 0≤min v 12 := le_min hv (by norm_num)
  have h1 := phi_clip_first (u:=u) hz hz40 hL hv hw
  have h2 : phi z (min u 12) (min v 12) w≤phi z (min u 12) v w ∧
      (phi z (min u 12) (min v 12) w=phi z (min u 12) v w ↔ v≤12) := by
    simpa only [phi_swap_uv z (min v 12) (min u 12) w,
      phi_swap_uv z v (min u 12) w] using phi_clip_first (u:=v) hz hz40 hL hu' hw
  have h3 : phi z (min u 12) (min v 12) (min w 12)≤phi z (min u 12) (min v 12) w ∧
      (phi z (min u 12) (min v 12) (min w 12)=phi z (min u 12) (min v 12) w ↔ w≤12) := by
    simpa only [phi_swap_uw z (min w 12) (min v 12) (min u 12),
      phi_swap_uw z w (min v 12) (min u 12)] using phi_clip_first (u:=w) hz hz40 hL hv' hu'
  refine ⟨h3.1.trans (h2.1.trans h1.1),?_⟩
  constructor
  · intro he
    have he1 := le_antisymm h1.1 (he.symm.trans_le (h3.1.trans h2.1))
    have he2 := le_antisymm h2.1 (h1.1.trans (he.symm.trans_le h3.1))
    have he3 := le_antisymm h3.1 (h2.1.trans (h1.1.trans he.ge))
    exact ⟨h1.2.mp he1,h2.2.mp he2,h3.2.mp he3⟩
  · rintro ⟨hu,hv,hw⟩
    simp only [min_eq_left hu,min_eq_left hv,min_eq_left hw]

/-- Precisely the remaining compact pointwise certificate obligation.
Its zero-set assertion is written in the original edge coordinates. -/
def CompactLogCertificate (z : ℝ) : Prop :=
  ∀ u∈Icc (0:ℝ) 12,∀ v∈Icc (0:ℝ) 12,∀ w∈Icc (0:ℝ) 12,
    0≤phi z u v w ∧ (phi z u v w=0 →
      Section02.AllowedPattern (branchA z) (branchB z)
        (Real.exp (-u)) (Real.exp (-v)) (Real.exp (-w)))

/-- Compact certificate positivity and its zero set extend to every
nonnegative logarithmic coordinate, with no additional tail assumption. -/
theorem log_certificate_of_compact {z : ℝ} (hz : 0<z) (hz40 : z≤1/40)
    (hL : branchLog z≤19/2) (hcompact : CompactLogCertificate z)
    {u v w : ℝ} (hu : 0≤u) (hv : 0≤v) (hw : 0≤w) :
    0≤phi z u v w ∧ (phi z u v w=0 →
      Section02.AllowedPattern (branchA z) (branchB z)
        (Real.exp (-u)) (Real.exp (-v)) (Real.exp (-w))) := by
  have hc := phi_clip hz hz40 hL hu hv hw
  have hbox := hcompact (min u 12) ⟨le_min hu (by norm_num),min_le_right _ _⟩
    (min v 12) ⟨le_min hv (by norm_num),min_le_right _ _⟩
    (min w 12) ⟨le_min hw (by norm_num),min_le_right _ _⟩
  refine ⟨hbox.1.trans hc.1,?_⟩
  intro he
  have hec : phi z (min u 12) (min v 12) (min w 12)=phi z u v w := by
    apply le_antisymm hc.1
    rw [he]
    exact hbox.1
  obtain ⟨hu12,hv12,hw12⟩ := hc.2.mp hec
  exact (hcompact u ⟨hu,hu12⟩ v ⟨hv,hv12⟩ w ⟨hw,hw12⟩).2 he

/-- The lower log bound of the manuscript family implies z<1/40. -/
theorem family_parameter_lt_one_fortieth {z : ℝ} (hz : 0<z) (hL : 39/10≤branchLog z) :
    z<1/40 := by
  have hl : Real.log 40<Real.log (1/z) := by
    change Real.log 40<branchLog z
    linarith [log_forty_bounds.2]
  have hi : (40:ℝ)<1/z := (Real.log_lt_log_iff (by norm_num) (one_div_pos.mpr hz)).mp hl
  have hh := (lt_div_iff₀ hz).mp hi
  linarith

/-- Full unbounded-domain family certificate, conditional ONLY on its compact
box verification. All tail and logarithmic-coordinate reductions are proved. -/
theorem family_certificate_of_compact {z : ℝ} (hz : 0<z)
    (hL : branchLog z∈Icc (39/10:ℝ) (19/2)) (hcompact : CompactLogCertificate z) :
    ∀ x∈Ioc (0:ℝ) 1,∀ y∈Ioc (0:ℝ) 1,∀ w∈Ioc (0:ℝ) 1,
      0≤psi z x y w ∧ (psi z x y w=0 →
        Section02.AllowedPattern (branchA z) (branchB z) x y w) := by
  intro x hx y hy w hw
  have hxlog : 0≤ -Real.log x := neg_nonneg.mpr (Real.log_nonpos hx.1.le hx.2)
  have hylog : 0≤ -Real.log y := neg_nonneg.mpr (Real.log_nonpos hy.1.le hy.2)
  have hwlog : 0≤ -Real.log w := neg_nonneg.mpr (Real.log_nonpos hw.1.le hw.2)
  have hh := log_certificate_of_compact hz (family_parameter_lt_one_fortieth hz hL.1).le hL.2 hcompact
    hxlog hylog hwlog
  simpa only [phi,neg_neg,Real.exp_log hx.1,Real.exp_log hy.1,Real.exp_log hw.1] using hh

/-- The second-coordinate version of `lem:certtail`. -/
theorem deriv_phi_second_pos {z u v w : ℝ} (hz : 0<z) (hz40 : z≤1/40)
    (hv : qA z+2≤v) (hu : 0≤u) (hw : 0≤w) :
    0<deriv (fun t => phi z u t w) v := by
  have he : (fun t => phi z u t w)=(fun t => phi z t u w) := funext fun t => phi_swap_uv z u t w
  rw [he]
  exact deriv_phi_first_pos hz hz40 hv hu hw

/-- The third-coordinate version of `lem:certtail`. -/
theorem deriv_phi_third_pos {z u v w : ℝ} (hz : 0<z) (hz40 : z≤1/40)
    (hw : qA z+2≤w) (hu : 0≤u) (hv : 0≤v) :
    0<deriv (fun t => phi z u v t) w := by
  have he : (fun t => phi z u v t)=(fun t => phi z t v u) := funext fun t => phi_swap_uw z u v t
  rw [he]
  exact deriv_phi_first_pos hz hz40 hw hv hu

/-- The already-proved contacts supply the converse zero-set implication. -/
theorem psi_zero_of_allowedPattern {z x y w : ℝ} (hz : 0<z) (hz40 : z≤1/40)
    (h : Section02.AllowedPattern (branchA z) (branchB z) x y w) : psi z x y w=0 := by
  obtain ⟨ha,hb,hc,hd⟩ := certificate_contacts hz hz40
  rcases h with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · exact ha.1
  · exact hb.1
  · exact hc.1
  · exact hd.1

/-- Full `prop:family`, including the exact zero set, reduced to the explicit
compact numerical certificate and no unproved analytic tail input. -/
theorem family_certificate_of_compact_exact {z : ℝ} (hz : 0<z)
    (hL : branchLog z∈Icc (39/10:ℝ) (19/2)) (hcompact : CompactLogCertificate z) :
    ∀ x∈Ioc (0:ℝ) 1,∀ y∈Ioc (0:ℝ) 1,∀ w∈Ioc (0:ℝ) 1,
      0≤psi z x y w ∧ (psi z x y w=0 ↔
        Section02.AllowedPattern (branchA z) (branchB z) x y w) := by
  intro x hx y hy w hw
  have hh := family_certificate_of_compact hz hL hcompact x hx y hy w hw
  exact ⟨hh.1,hh.2,psi_zero_of_allowedPattern hz (family_parameter_lt_one_fortieth hz hL.1).le⟩

end SparseLowerTail.Certificate
