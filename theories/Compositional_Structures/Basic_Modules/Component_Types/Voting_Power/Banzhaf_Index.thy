theory Banzhaf_Index
  imports Simple_Voting_Game_Comparison

begin

section \<open>Banzhaf Index Definitions\<close>

(* TODO definition of swing votes is now in 3 places, don't do that :( *)
fun swing_vote_svg :: "'v set set \<Rightarrow> 'v \<Rightarrow> 'v set \<Rightarrow> ereal" where
  "swing_vote_svg \<F> v S = (if ((S \<union> {v}) \<in> \<F>) \<noteq> ((S - {v}) \<in> \<F>) then 1 else 0)"

text \<open>
  First formulation of a Banzhaf index for simple voting games:
  Count the number of coalitions a voter can change by switching their vote and average over those.
\<close>

fun banzhaf_svg_1 :: "('v Simple_Voting_Game, 'v) Voting_Power" where
  "banzhaf_svg_1 (V, \<F>) v = 
    (if v \<notin> V then 0 else (1/(2^(card V))) * (\<Sum> S \<in> Pow V. swing_vote_svg \<F> v S))"
(* TODO: Original definition just assumes finite voter sets.
Formalizing the indices here forces one to explicitly think about infinite sets 
since every statement about the index includes infinite sets in its domain. 
Here, we define each voter's power to be 0 if V is infinite.*)

lemma infinite_voter_set_zero_banzhaf:
  fixes V :: "'v set" and \<F> :: "'v set set" and v :: 'v
  assumes "infinite V"
  shows "banzhaf_svg_1 (V, \<F>) v = 0"
  using assms finite_Pow_iff sum.infinite
  by simp

section \<open>Auxiliary Lemmas\<close>

lemma image_inj:
  fixes \<sigma> :: "'x \<Rightarrow> 'x"
  assumes "inj \<sigma>"
  shows "inj (image \<sigma>)"
proof
  fix X :: "'x set" and Y :: "'x set"
  assume "\<sigma> ` X = \<sigma> ` Y"
  thus "X = Y"
    using assms
    by (simp add: inj_image_eq_iff)
qed

lemma swing_vote_implication:
  fixes
    C :: "'v set" and
    \<F> :: "'v set set" and
    v :: 'v and
    \<sigma> :: "'v \<Rightarrow> 'v"
  assumes "C \<in> \<F>"
  shows "(\<sigma> ` C) \<in> {\<sigma> ` C | C. C \<in> \<F>}"
  using assms
  by blast

lemma swing_vote_equivalence:
  fixes
    C :: "'v set" and
    \<F> :: "'v set set" and
    v :: 'v and
    \<sigma> :: "'v \<Rightarrow> 'v"
  assumes
    "bij \<sigma>"
  shows
    "swing_vote_svg \<F> v C = swing_vote_svg {\<sigma> ` C | C. C \<in> \<F>} (\<sigma> v) (\<sigma> ` C)"
proof - 
  have "\<sigma> ` (C - {v}) = \<sigma> ` C - {\<sigma> v}"
    using assms
    by (simp add: bij_betw_def image_set_diff)
  hence "((C - {v}) \<in> \<F>) \<longleftrightarrow> ((\<sigma> ` C - {\<sigma> v}) \<in> {\<sigma> ` C | C. C \<in> \<F>})"
    using assms swing_vote_implication[of "C - {v}" \<F> \<sigma>] 
          swing_vote_implication[of "\<sigma> ` C - {\<sigma> v}" "{\<sigma> ` C | C. C \<in> \<F>}" "the_inv \<sigma>"]
    by (metis (mono_tags, lifting) bij_img_containment)
  moreover have"((C \<union> {v}) \<in> \<F>) \<longleftrightarrow> ((\<sigma> ` C \<union> {\<sigma> v}) \<in> {\<sigma> ` C | C. C \<in> \<F>})"
    using assms swing_vote_implication[of "C \<union> {v}" \<F> \<sigma>] 
          swing_vote_implication[of "\<sigma> ` C \<union> {\<sigma> v}" "{\<sigma> ` C | C. C \<in> \<F>}" "the_inv \<sigma>"]
    by (metis (no_types, lifting) ext Un_commute 
        bij_img_containment image_insert insert_is_Un)
  ultimately show ?thesis
    by simp
qed

section \<open>Banzhaf Voting Power Index\<close>

text \<open>
We call a voting power index (axiom-based) Banzhaf index if it satisfies the extended formulation
of the monotone simple voting game Banzhaf index axiomatization, i.e., 
the null player, total power, symmetry and transfer axioms.
\<close>
locale banzhaf_index_axioms =
  np: null_player_axiom domain semantics \<Phi>_np sv +
  tp: total_power_axiom domain semantics \<Phi>_tp sv +
  sym: symmetry_axiom domain semantics \<Phi>_sym \<psi> +
  tf: transfer_axiom domain semantics \<Phi>_tf result_tf reachability
    for semantics :: "('\<tau>, 'v, 'b, 'r) Voting_Rule_Transformation" and 
        domain sv result_tf reachability \<psi> \<Phi>_np \<Phi>_tp \<Phi>_sym \<Phi>_tf
begin

sublocale vp_axiom: voting_power_axiom domain semantics "\<Phi>_np \<union> \<Phi>_tp \<union> \<Phi>_sym \<union> \<Phi>_tf"
  by (rule local.np.voting_power_axiom_axioms)

end

fun (in banzhaf_index_axioms) is_axm_banzhaf_index :: "('\<tau>, 'v) Voting_Power \<Rightarrow> bool" where
  "is_axm_banzhaf_index \<delta> = (vp_axiom.satisfies \<delta>)"

text \<open>
We call a voting power index (probability-based) Banzhaf index if it measures the probability of 
having a swing vote according to some probability space on the ballot profiles.
\<close>
locale banzhaf_index_probability = ipower_axiom domain semantics \<Phi>_ipow space event
  for domain :: "'\<tau> set" and semantics :: "('\<tau>, 'v, 'b, 'r) Voting_Rule_Transformation" and
      space event sv \<Phi>_ipow +
  assumes
    swing_vote_predicate: "swing_vote_predicate sv" and
    swing_vote_event: "event = swings sv"

fun (in banzhaf_index_probability) is_prob_banzhaf_index :: "('\<tau>, 'v) Voting_Power \<Rightarrow> bool" where
  "is_prob_banzhaf_index \<delta> = (satisfies \<delta>)"

text \<open>
We may call a voting power index a Banzhaf index if, in situations that can be modelled as 
monotone simple voting games, it behaves like the original Banzhaf index on simple voting games.
\<close>
locale banzhaf_index_comparison = comp: svg_model_comparison 
  "finite_monotone_SVGs :: 'v Simple_Voting_Game set" b1 b2 r1 r2 domain semantics model_equivalence 
  for b1 :: 'b and b2 and r1 :: 'r and r2 and semantics and domain :: "'\<tau> set" and model_equivalence

fun (in banzhaf_index_comparison) is_comp_banzhaf_index :: "('\<tau>, 'v) Voting_Power \<Rightarrow> bool" where
  "is_comp_banzhaf_index \<delta> = (comp.svg_comp.power_equality banzhaf_svg_1 \<delta>)"
 
section \<open>Simple Voting Game Banzhaf Index\<close>

theorem (in simple_voting_game_model) svg_banzhaf_sat_null_player:
  "svg_np_axiom.satisfies banzhaf_svg_1"
proof (simp, safe)
fix
    V :: "'v set" and
    \<F> :: "'v set set" and
    v :: 'v
  assume "(V, \<F>) \<in> S" and
    "v \<in> mod.voters (V, \<F>)" and
    "svg_swing (V, \<F>) v = (\<lambda>p. False)"
  moreover have 
    "\<forall>C \<subseteq> V. ((C \<union> {v}) \<in> \<F>) \<noteq> ((C - {v}) \<in> \<F>) \<longrightarrow> svg_swing (V, \<F>) v (svg_profile (V, \<F>) C)"
    by auto
  ultimately have "\<forall>C \<subseteq> V. ((C \<union> {v}) \<in> \<F>) = ((C - {v}) \<in> \<F>)"
    by metis
  hence "\<forall>C \<in> Pow V. swing_vote_svg \<F> v C = 0"
    by simp
  thus "banzhaf_svg_1 (V, \<F>) v = 0"
    by simp
qed

theorem (in simple_voting_game_model) svg_banzhaf_sat_symmetry:
  "svg_sym_axiom.satisfies banzhaf_svg_1"
proof (simp, safe)
fix
    V :: "'v set" and \<F> :: "'v set set" and \<sigma> :: "'v \<Rightarrow> 'v" and v :: 'v
  assume
    "(V, \<F>) \<in> S" and
    "bij \<sigma>" and
    "\<Phi>_svg \<sigma> (V, \<F>) \<in> S" and
    "v \<in> mod.voters (V, \<F>)"
  thus "banzhaf_svg_1 (V, \<F>) v = banzhaf_svg_1 (\<Phi>_svg \<sigma> (V, \<F>)) (\<sigma> v)"
  proof (cases "finite V")
    case True
    hence fin: "finite {S |S. S \<subseteq> V \<and> swing_vote_svg \<F> v S = 1}"
      by simp
    have inj_img: "inj_on ((`) \<sigma>) {S |S. S \<subseteq> V \<and> swing_vote_svg \<F> v S = 1}"
      using \<open>bij \<sigma>\<close> image_inj[of \<sigma>] inj_on_subset 
      unfolding bij_def
      by blast
    have "finite (Pow V)"
      using True
      by simp
    moreover have "\<forall>S. swing_vote_svg \<F> v S = of_bool (swing_vote_svg \<F> v S = 1)"
      by simp
    ultimately have 
      "(\<Sum> S \<in> Pow V. swing_vote_svg \<F> v S) = card (Pow V \<inter> {x. swing_vote_svg \<F> v x = 1})"
      using sum_of_bool_eq[of "Pow V" "\<lambda>S. swing_vote_svg \<F> v S = 1"]
        of_bool_eq(1,2) one_ereal_def sum.cong sum_ereal zero_ereal_def
      sorry
    moreover have 
      "Pow V \<inter> {x. swing_vote_svg \<F> v x = 1} = {S | S. S \<in> Pow V \<and> swing_vote_svg \<F> v S = 1}"
      by blast
    ultimately have 
      "(\<Sum> S \<in> Pow V. swing_vote_svg \<F> v S) = card {S | S. S \<subseteq> V \<and> swing_vote_svg \<F> v S = 1}"
      by simp
    also have "... = card (image (image \<sigma>) {S | S. S \<subseteq> V \<and> swing_vote_svg \<F> v S = 1})"
      using inj_img
            inj_on_iff_eq_card[of "{S | S. S \<subseteq> V \<and> swing_vote_svg \<F> v S = 1}" "image \<sigma>", OF fin]
      by presburger
    also have "... = card {\<sigma> ` S | S. S \<subseteq> V \<and> swing_vote_svg \<F> v S = 1}"
      using Setcompr_eq_image[of "image \<sigma>" "{S | S. S \<subseteq> V \<and> swing_vote_svg \<F> v S = 1}"]
      by simp
    also have "... = card {\<sigma> ` S | S. S \<subseteq> V \<and> swing_vote_svg {\<sigma> ` C | C. C \<in> \<F>} (\<sigma> v) (\<sigma> ` S) = 1}"
      using swing_vote_equivalence[of \<sigma> \<F> v, OF \<open>bij \<sigma>\<close>]
      by metis
    also have "... = card {S' | S'. S' \<subseteq> \<sigma> ` V \<and> swing_vote_svg {\<sigma> ` C | C. C \<in> \<F>} (\<sigma> v) S' = 1}"
      using \<open>bij \<sigma>\<close>
      by (metis (no_types, lifting) image_mono subset_imageE)
    finally have "(\<Sum> S \<in> Pow V. swing_vote_svg \<F> v S) = 
      card {S' | S'. S' \<subseteq> \<sigma> ` V \<and> swing_vote_svg {\<sigma> ` C | C. C \<in> \<F>} (\<sigma> v) S' = 1}"
      by simp
    hence rewrite_1: "banzhaf_svg_1 (V, \<F>) v = (if v \<notin> V then 0 else (1/(2^(card V))) * 
      (card {S' | S'. S' \<subseteq> \<sigma> ` V \<and> swing_vote_svg {\<sigma> ` C | C. C \<in> \<F>} (\<sigma> v) S' = 1}))"
      using True
      by simp
    have "finite (Pow (\<sigma> ` V))"
      using True
      by simp
    moreover have "\<forall>S. swing_vote_svg {\<sigma> ` C | C. C \<in> \<F>} (\<sigma> v) S = 
      of_bool (swing_vote_svg {\<sigma> ` C | C. C \<in> \<F>} (\<sigma> v) S = 1)" 
      (* TODO rewrite proof to make it less repetitive *)
      by simp
    ultimately have 
      "(\<Sum> S \<in> Pow (\<sigma> ` V). swing_vote_svg {\<sigma> ` C | C. C \<in> \<F>} (\<sigma> v) S) = 
        card (Pow (\<sigma> ` V) \<inter> {x. swing_vote_svg {\<sigma> ` C | C. C \<in> \<F>} (\<sigma> v) x = 1})"
      using sum_of_bool_eq[of "Pow (\<sigma> ` V)" "\<lambda>S. swing_vote_svg {\<sigma> ` C | C. C \<in> \<F>} (\<sigma> v) S = 1"]
        of_bool_eq(1,2) one_ereal_def sum.cong sum_ereal zero_ereal_def
      sorry
    moreover have 
      "Pow (\<sigma> ` V) \<inter> {x. swing_vote_svg {\<sigma> ` C | C. C \<in> \<F>} (\<sigma> v) x = 1} = 
        {S | S. S \<in> Pow (\<sigma> ` V) \<and> swing_vote_svg {\<sigma> ` C | C. C \<in> \<F>} (\<sigma> v) S = 1}"
      by blast
    ultimately have
      "(\<Sum> S \<in> Pow (\<sigma> ` V). swing_vote_svg {\<sigma> ` C | C. C \<in> \<F>} (\<sigma> v) S) = 
        card {S | S. S \<subseteq> (\<sigma> ` V) \<and> swing_vote_svg {\<sigma> ` C | C. C \<in> \<F>} (\<sigma> v) S = 1}"
      by simp
    hence rewrite_2: "banzhaf_svg_1 (\<Phi>_svg \<sigma> (V, \<F>)) (\<sigma> v) = 
      (if \<sigma> v \<notin> \<sigma> ` V then 0 else (1/(2^(card (\<sigma> ` V)))) * 
        (card {S | S. S \<subseteq> (\<sigma> ` V) \<and> swing_vote_svg {\<sigma> ` C | C. C \<in> \<F>} (\<sigma> v) S = 1}))"
      using True
      by simp
    moreover have "\<sigma> v \<notin> \<sigma> ` V \<longleftrightarrow> v \<notin> V"
      using \<open>bij \<sigma>\<close>
      by (simp add: bij_betw_def inj_image_mem_iff)
    moreover have "card V = card (\<sigma> ` V)"
      using True \<open>bij \<sigma>\<close>
      by (metis \<open>bij \<sigma>\<close> True UNIV_I bij_betw_def Pow_UNIV Pow_iff inj_on_iff_eq_card inj_on_subset)
    ultimately show ?thesis
      using True rewrite_1
      by presburger
  next
    case False
    hence "infinite (\<sigma> ` V)"
      using \<open>bij \<sigma>\<close>
      by (metis \<open>bij \<sigma>\<close> False UNIV_I inj_on_def bij_def finite_imageD)
    then show ?thesis
      using False 
      by simp
  qed 
qed

theorem (in simple_voting_game_model) svg_banzhaf_sat_total_power:
  "svg_tp_axiom.satisfies banzhaf_svg_1"
  sorry

theorem (in simple_voting_game_model) svg_banzhaf_sat_transfer:
  assumes
    "S \<subseteq> monotone_SVGs"
  shows
    axiom_satisfied: "svg_tf_axiom.satisfies banzhaf_svg_1"
proof (simp only: svg_tf_axiom.satisfies.simps, unfold mod.transfer_ax.simps, safe)
  fix
    V :: "'v set" and
    V' :: "'v set" and
    \<F> :: "'v set set" and
    \<F>' :: "'v set set" and
    p :: "('v, 'b) Profile" and
    r :: 'r and
    v :: 'v
  assume
    "(V, \<F>) \<in> S" and "(V', \<F>') \<in> S" and
    prof: "p \<in> mod.profiles (V, \<F>)" and
    vot: "v \<in> mod.voters (V, \<F>)" and
    "r \<in> mod.results (V, \<F>)" and
    eq_V_V': "mod.voters (V, \<F>) = mod.voters (V', \<F>')" and
    eq_B_B': "mod.ballots (V, \<F>) = mod.ballots (V', \<F>')" and
    eq_R_R': "mod.results (V, \<F>) = mod.results (V', \<F>')" and
    eq_res: "\<forall>q \<in> reachability_svg p v. mod.aggregation (V, \<F>) q = mod.aggregation (V', \<F>') q"
  let ?G' = "result_transform_svg p r (V, \<F>)"
  let ?G'' = "result_transform_svg p r (V', \<F>')"
  let ?C = "preimg_in V p {ballot1}"
  have eq_vot: "svg_voters ?G' = V"
    unfolding result_transform_svg.simps Let_def
    by simp
  have eq_vot':  "svg_voters ?G'' = V"
    unfolding result_transform_svg.simps Let_def
    using eq_V_V'
    by simp
  show
    "banzhaf_svg_1 ?G' v - banzhaf_svg_1 (V, \<F>) v = 
      banzhaf_svg_1 ?G'' v - banzhaf_svg_1 (V', \<F>') v"
  proof (cases "r = result1")
    case True
    hence "?G' = (V, \<F> \<union> {?C})"
      by simp
    have "?G'' = (V, \<F>' \<union> {?C})"
      using eq_V_V' True
      by simp
    show ?thesis
    proof (cases "?C \<in> \<F>")
      case True
      then show ?thesis sorry
    next
      case False
      then show ?thesis sorry
    qed
  next
    case False
    hence "?G' = (V, \<F> - {?C})"
      by simp
    have "?G'' = (V, \<F>' - {?C})"
      using eq_V_V' False
      by simp
    show ?thesis
    proof (cases "?C \<in> \<F>")
      case True
      then show ?thesis sorry
    next
      case False
      then show ?thesis sorry
    qed
  qed
qed

section \<open>Simple Voting Game Banzhaf Index Instantiations\<close>

sublocale simple_voting_game_model \<subseteq> svg_banzhaf_index_axioms: banzhaf_index_axioms svg_sem S 
  svg_swing result_transform_svg reachability_svg \<Phi>_svg
  "{mod.null_player_ax svg_swing}"
  "{mod.total_power_ax svg_swing}"
  "{mod.symmetry_ax \<Phi>_svg}"
  "{mod.transfer_ax result_transform_svg reachability_svg}"
  unfolding banzhaf_index_axioms_def
  by (metis svg_np_axiom.null_player_axiom_axioms svg_tp_axiom.total_power_axiom_axioms 
            svg_sym_axiom.symmetry_axiom_axioms svg_tf_axiom.transfer_axiom_axioms)

sublocale finite_simple_voting_game_model \<subseteq> svg_banzhaf_index_probability: 
  banzhaf_index_probability S svg_sem uniform_distr_voters svg_swings svg_swing
    "{mod.is_ipower uniform_distr_voters svg_swings}"
proof (unfold_locales, rule local.svg_np_axiom.swing_vote_predicate, standard, standard)
  fix G :: "'v Simple_Voting_Game" and v :: 'v
  have "svg_swings G v = {svg_profile G X | X. swing_coalition G v X}"
    using svg_swings.elims 
    by (metis (no_types, lifting) ext)
  moreover have "mod.swings svg_swing G v = {p | p. p \<in> mod.profiles G \<and> svg_swing G v p}"
    by simp
  moreover have 
    "{svg_profile G X | X. swing_coalition G v X} = {p | p. p \<in> mod.profiles G \<and> svg_swing G v p}"
    sorry
  ultimately show "svg_swings G v = mod.swings svg_swing G v"
    by metis
qed
  
sublocale simple_voting_game_model \<subseteq> svg_banzhaf_index_comparison: 
  banzhaf_index_comparison ballot1 ballot2 result1 result2 svg_sem S "(=)"
  using simple_voting_game_model_axioms
  unfolding simple_voting_game_model_def simple_voting_game_model_axioms_def
  by (unfold_locales, simp_all, 
      unfold Pi_def finite_monotone_SVGs_def valid_simple_voting_games_def, simp_all)

text \<open>
  The Banzhaf Index as defined by banzhaf_svg_1 on monotone SVGs satisfies the Banzhaf Index axioms.
\<close>

theorem (in simple_voting_game_model) monotone_SVG_banzhaf_sat_axioms: 
  assumes "S \<subseteq> monotone_SVGs"
  shows "svg_banzhaf_index_axioms.is_axm_banzhaf_index banzhaf_svg_1"
  using svg_banzhaf_sat_symmetry svg_banzhaf_sat_null_player
    svg_banzhaf_sat_total_power svg_banzhaf_sat_transfer[OF assms] 
  unfolding svg_banzhaf_index_axioms.is_axm_banzhaf_index.simps 
        svg_banzhaf_index_axioms.vp_axiom.satisfies.simps
        svg_sym_axiom.satisfies.simps svg_np_axiom.satisfies.simps 
        svg_tp_axiom.satisfies.simps svg_tf_axiom.satisfies.simps
  by blast

theorem (in simple_voting_game_model) unique_banzhaf_axioms_helper:
  fixes f :: "'v Simple_Voting_Game \<Rightarrow> 'v \<Rightarrow> ereal"
  shows "svg_banzhaf_index_axioms.vp_axiom.uniqueness_in {\<delta> |\<delta>. (\<forall>G. G \<notin> S \<longrightarrow> \<delta> G = f G)}"
  sorry

text \<open>
  The Banzhaf Index as defined by banzhaf_svg_1 on finite SVGs measures the uniformly distributed
  probability of having a swing vote.
\<close>

lemma banzhaf_gte_0: 
  fixes V :: "'v set" and \<F> :: "'v set set" and v :: 'v  
  shows "0 \<le> banzhaf_svg_1 (V, \<F>) v"
  by (simp add: sum_nonneg)

lemma (in simple_voting_game_model) banzhaf_rewrite:
  fixes V :: "'v set" and \<F> :: "'v set set" and v :: 'v  
  shows
    "banzhaf_svg_1 (V, \<F>) v = card (svg_swings (V, \<F>) v) / card (Pow V)"
  sorry

theorem (in finite_simple_voting_game_model) SVG_banzhaf_is_probability:
  shows "svg_banzhaf_index_probability.is_prob_banzhaf_index banzhaf_svg_1"
proof (simp, safe, rule banzhaf_gte_0)
  fix V :: "'v set" and \<F> :: "'v set set" and v :: 'v
  assume "(V, \<F>) \<in> S" and "v \<in> rule_voters (svg_sem (V, \<F>))"
  moreover have "V = fst (V, \<F>)"
    by simp
  ultimately have fin_vot: "finite V"
    using finite_voters svg_voters_fst
    by metis
  have "space (uniform_distr_voters (V, \<F>) v) = svg_profile (V, \<F>) ` Pow V"
    unfolding uniform_distr_voters.simps uniform_count_measure_def
    by (rule Nonnegative_Lebesgue_Integration.space_point_measure)
  moreover have "finite (Pow V)"
    using fin_vot
    by simp
  moreover with this have "finite (svg_profile (V, \<F>) ` Pow V)"
    by simp
  moreover have "svg_swings (V, \<F>) v \<subseteq> svg_profile (V, \<F>) ` Pow V"
    by auto
  ultimately have "enn2ereal (emeasure (uniform_distr_voters (V, \<F>) v) (svg_swings (V, \<F>) v))
    = card (svg_swings (V, \<F>) v) / card (svg_profile (V, \<F>) ` Pow V)"
    unfolding uniform_distr_voters.simps
    using emeasure_uniform_count_measure[of "svg_profile (V, \<F>) ` Pow V" "svg_swings (V, \<F>) v"]
    by simp
  moreover have 
    "banzhaf_svg_1 (V, \<F>) v = card (svg_swings (V, \<F>) v) / card (Pow V)"
    unfolding banzhaf_svg_1.simps
    using banzhaf_rewrite
    by simp
  moreover have "card (Pow V) = card (svg_profile (V, \<F>) ` Pow V)"
    sorry
  ultimately show "banzhaf_svg_1 (V, \<F>) v = 
    enn2ereal (emeasure (uniform_distr_voters (V, \<F>) v) (svg_swings (V, \<F>) v))"
    by metis
qed

text \<open>
  The Banzhaf Index as defined by banzhaf_svg_1 on SVGs coincides with itself when restricted to
  finite monotone SVGs.
\<close>

theorem (in simple_voting_game_model) SVG_banzhaf_coincides_with_restriction:
  shows "svg_banzhaf_index_comparison.is_comp_banzhaf_index banzhaf_svg_1"
  unfolding svg_banzhaf_index_comparison.is_comp_banzhaf_index.simps 
            svg_banzhaf_index_comparison.comp.svg_comp.power_equality.simps
  by simp

end