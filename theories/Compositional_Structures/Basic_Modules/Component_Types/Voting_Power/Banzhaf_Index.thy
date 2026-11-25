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

subsection \<open>Auxiliary Lemmas\<close>

lemma ereal_helpers:
  fixes 
    condition :: bool and f :: "'x \<Rightarrow> nat" and X :: "'x set" and x :: real and y :: real
  shows 
    ereal_ite_helper: 
      "ereal (real (if condition then 1 else 0)) = (if condition then (1::ereal) else 0)" and
    ereal_sum_helper: 
      "(\<Sum>x \<in> X. ereal (f x)) = ereal (\<Sum>x \<in> X. f x)" and
    ereal_div_helper:
      "y \<noteq> 0 \<Longrightarrow> ereal (x / y) = (ereal x) / (ereal y)"
  by simp+

lemma sum_subtractf_ereal:
  fixes f g :: "'a \<Rightarrow> ereal" and A :: "'a set"
  assumes "\<forall>a \<in> A. \<bar>f a\<bar> \<noteq> \<infinity> \<and> \<bar>g a\<bar> \<noteq> \<infinity>"
  shows "(\<Sum>x\<in>A. f x - g x) = (\<Sum>x\<in>A. f x) - (\<Sum>x\<in>A. g x)"
proof -
  have fin_diff: "\<forall>a \<in> A. \<bar>(f-g) a\<bar> \<noteq> \<infinity>"
    using assms ereal_diff_eq_MInfty_iff ereal_minus_eq_PInfty_iff 
    by auto
  hence "real_of_ereal (\<Sum>x\<in>A. f x - g x) = (\<Sum>x\<in>A. real_of_ereal (f x - g x))"
    using sum_real_of_ereal[of A "f-g"]
    by (metis (no_types, lifting) minus_apply sum.cong)
  also have "... = (\<Sum>x\<in>A. real_of_ereal (f x) - real_of_ereal (g x))"
    using assms real_of_ereal_minus' by simp
  also have "... = (\<Sum>x\<in>A. real_of_ereal (f x)) - (\<Sum>x\<in>A. real_of_ereal (g x))"
    using sum_subtractf
    by metis
  also have "... = real_of_ereal (\<Sum>x\<in>A. f x) - real_of_ereal (\<Sum>x\<in>A. g x)"
    using assms sum_real_of_ereal[of A f] sum_real_of_ereal[of A g]
    by metis
  also have "... = real_of_ereal ((\<Sum>x\<in>A. f x) - (\<Sum>x\<in>A. g x))"
    using assms by (metis real_of_ereal_minus' sum_Inf)
  finally have "real_of_ereal (\<Sum>x\<in>A. f x - g x) = real_of_ereal ((\<Sum>x\<in>A. f x) - (\<Sum>x\<in>A. g x))"
    by simp
  moreover have "\<bar>(\<Sum>x\<in>A. f x - g x)\<bar> \<noteq> \<infinity>"
    using fin_diff
    by (metis (no_types, lifting) minus_apply sum_Inf)
  moreover have "\<bar>(\<Sum>x\<in>A. f x) - (\<Sum>x\<in>A. g x)\<bar> \<noteq> \<infinity>"
    using assms sum_Inf[of f A] sum_Inf[of g A]
    by auto
  ultimately show ?thesis
    by auto
qed

lemma banzhaf_gte_0: 
  fixes V :: "'v set" and \<F> :: "'v set set" and v :: 'v  
  shows "0 \<le> banzhaf_svg_1 (V, \<F>) v"
  by (simp add: sum_nonneg)

lemma banzhaf_svg_finite: 
  fixes V :: "'v set" and \<F> :: "'v set set" and v :: 'v
  shows "\<bar>banzhaf_svg_1 (V, \<F>) v\<bar> \<noteq> \<infinity>"
proof (cases "finite V")
  case True
  hence "finite (Pow V)"
    by simp
  hence "(\<Sum> S \<in> Pow V. swing_vote_svg \<F> v S) \<noteq> \<infinity>"
    using sum_Pinfty[of _ "Pow V"]
    by simp
  moreover have "(\<Sum> S \<in> Pow V. swing_vote_svg \<F> v S) \<ge> 0"
    by (simp add: sum_nonneg)
  ultimately have "\<bar>(\<Sum> S \<in> Pow V. swing_vote_svg \<F> v S)\<bar> \<noteq> \<infinity>"
    by simp
  moreover have "\<bar>(1/((2::ereal) ^ card V))\<bar> \<noteq> \<infinity>"
    by simp
  ultimately have "\<bar>(1/(2 ^ card V)) * (sum (swing_vote_svg \<F> v) (Pow V))\<bar> \<noteq> \<infinity>"
    using sum_Inf 
    by auto
  thus ?thesis
    by simp
next
  case False
  hence "banzhaf_svg_1 (V, \<F>) v = 0"
    by simp
  thus ?thesis by simp
qed

lemma sum_div_ereal:
  fixes f :: "'a \<Rightarrow> ereal" and A :: "'a set" and x :: ereal
  assumes "\<forall>a \<in> A. \<bar>f a\<bar> \<noteq> \<infinity>" and "\<forall>a \<in> A. 0 \<le> f a"
  shows "(\<Sum>a \<in> A. f a / x) = (\<Sum>a \<in> A. f a) / x"
proof -
  have "(\<Sum>a \<in> A. f a / x) = (\<Sum>a \<in> A. (1/x) * f a)"
    by simp
  also have "... = (1/x) * (\<Sum>a \<in> A. f a)"
    using assms sum_ereal_right_distrib[of A f "1/x"]
    by metis
  also have "... = (\<Sum>a \<in> A. f a) / x"
    by simp
  finally show ?thesis
    by metis
qed  

text \<open>
  Note that this also holds for empty V since Isabelle defines 0/0 = 0 in the natural numbers.
\<close>
lemma (in finite_simple_voting_game_model) banzhaf_rewrite:
  fixes V :: "'v set" and \<F> :: "'v set set" and v :: 'v  
  assumes "(V, \<F>) \<in> S"
  shows
    "banzhaf_svg_1 (V, \<F>) v = card (svg_swings (V, \<F>) v) / card (Pow V)"
proof (unfold banzhaf_svg_1.simps, split if_split, safe)
  assume "v \<notin> V"
  hence "card (svg_swings (V, \<F>) v) = 0"
    by simp
  thus "0 = ereal (real (card (svg_swings (V, \<F>) v)) / real (card (Pow V)))"
    by simp
next
  assume 
    "v \<in> V" and 
    neq: 
      "1 / 2 ^ card V * sum (swing_vote_svg \<F> v) (Pow V) \<noteq>
        ereal (real (card (svg_swings (V, \<F>) v)) / real (card (Pow V)))"
  let ?swings = "{C | C. swing_coalition (V, \<F>) v C}"
  let ?non_swings = "{C | C. C \<subseteq> V \<and> \<not> swing_coalition (V, \<F>) v C}"
  have fin: "finite (Pow V)"
    using finite_voters assms
    by auto
  have "\<forall>S \<in> Pow V. S \<in> ?swings \<or> S \<in> ?non_swings"
    by auto
  hence "Pow V \<subseteq> ?swings \<union> ?non_swings"
    by auto
  moreover have subset: "?swings \<union> ?non_swings \<subseteq> Pow V"
    by auto
  ultimately have part: "Pow V = ?swings \<union> ?non_swings"
    by order
  moreover have "?swings \<inter> ?non_swings = {}"
    by auto
  moreover have fin_swings: "finite ?swings"
    using subset fin
    by simp
  moreover have fin_non_swings: "finite ?non_swings"
    using subset fin
    by simp
  ultimately have "(\<Sum>C \<in> Pow V. swing_vote_svg \<F> v C) = 
    (\<Sum>C \<in> ?swings. swing_vote_svg \<F> v C) + (\<Sum>C \<in> ?non_swings. swing_vote_svg \<F> v C)"
    by (metis (no_types, lifting) sum.union_disjoint)
  also have "(\<Sum>C \<in> ?swings. swing_vote_svg \<F> v C) = (\<Sum>C \<in> ?swings. (1::ereal))"
    by simp
  also have "(\<Sum>C \<in> ?swings. (1::ereal)) = card ?swings"
    using card_eq_sum[of ?swings]
    by (simp add: one_ereal_def)
  also have "(\<Sum>C \<in> ?non_swings. swing_vote_svg \<F> v C) = (\<Sum>C \<in> ?swings. 0)"
    using \<open>v \<in> V\<close> by simp
  also have "(\<Sum>C \<in> ?swings. (0::ereal)) = 0"
    by simp
  finally have
    "(\<Sum>C \<in> Pow V. swing_vote_svg \<F> v C) = (card ?swings)"
    by simp
  hence
    "(\<Sum>C \<in> Pow V. swing_vote_svg \<F> v C) / ereal (2 ^ card V) = (card ?swings) / ereal (2 ^ card V)"
    by metis
  moreover have "ereal (2 ^ card V) = card (Pow V)"
    using finite_voters assms card_Pow[of V] 
    by auto
  ultimately have rewrite_sum:
    "(\<Sum>C \<in> Pow V. swing_vote_svg \<F> v C) / ereal (2 ^ card V) = card ?swings / ereal (card (Pow V))"
    by metis
  also have "... = card (svg_swings (V, \<F>) v) / ereal (card (Pow V))"
    using swing_cardinality
    by metis
  also have "... = ereal (real (card (svg_swings (V, \<F>) v)) / real (card (Pow V)))"
    using fin by auto
  finally have "1 / 2 ^ card V * sum (swing_vote_svg \<F> v) (Pow V) =
    ereal (real (card (svg_swings (V, \<F>) v)) / real (card (Pow V)))"
    by simp
  thus "False"
    using neq
    by metis
qed      

lemma (in finite_simple_voting_game_model) card_profiles:
  assumes "(V, \<F>) \<in> S"
  shows 
    "card (mod.ballots (V, \<F>)) ^ card (rule_voters (svg_sem (V, \<F>))) = card (Pow V)"
proof -
  have "finite V"
    using assms finite_simple_voting_game_model_axioms
    unfolding finite_simple_voting_game_model_def finite_simple_voting_game_model_axioms_def
    by auto
  have "mod.ballots (V, \<F>) = {ballot1, ballot2}"
    using finite_simple_voting_game_model_axioms
    unfolding finite_simple_voting_game_model_def simple_voting_game_model_def
    by simp
  moreover have "card {ballot1, ballot2} = 2"
    using finite_simple_voting_game_model_axioms
    unfolding finite_simple_voting_game_model_def simple_voting_game_model_def
              simple_voting_game_model_axioms_def
    by simp
  ultimately have "card (mod.ballots (V, \<F>)) = 2"
    by simp
  hence "card (mod.ballots (V, \<F>)) ^ card (rule_voters (svg_sem (V, \<F>))) = 
    2 ^ card (rule_voters (svg_sem (V, \<F>)))"
    by metis
  also have "... = card (Pow V)"
    using \<open>finite V\<close>
    by (simp add: card_Pow)
  finally show ?thesis
    by simp
qed

subsection \<open>Axiom Instantiations\<close>

theorem (in simple_voting_game_model) svg_banzhaf_sat_null_player:
  "svg_np_axiom.satisfies banzhaf_svg_1"
proof (simp, safe)
fix
    V :: "'v set" and
    \<F> :: "'v set set" and
    v :: 'v
  assume "(V, \<F>) \<in> S" and
    vot: "v \<in> mod.voters (V, \<F>)" and
    "svg_swing (V, \<F>) v = (\<lambda>p. False)"
  moreover have 
    "\<forall>C \<subseteq> V. ((C \<union> {v}) \<in> \<F>) \<noteq> ((C - {v}) \<in> \<F>) \<longrightarrow> svg_swing (V, \<F>) v (svg_profile (V, \<F>) C)"
    using vot
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

theorem (in finite_simple_voting_game_model) svg_banzhaf_sat_total_power:
  "svg_tp_axiom.satisfies banzhaf_svg_1"
proof (unfold svg_tp_axiom.satisfies.simps mod.total_power_ax.simps, safe)
  fix
    V :: "'v set" and
    \<F> :: "'v set set"
  assume "(V, \<F>) \<in> S"
  let ?g = "\<lambda>v. ereal (real (card (mod.swings svg_swing (V, \<F>) v))) /
        ereal (real (card (mod.ballots (V, \<F>)) ^ card (rule_voters (svg_sem (V, \<F>)))))"
  let ?h = "\<lambda>v. ereal (real (card (mod.swings svg_swing (V, \<F>) v)))"
  let ?x = "ereal (real (card (mod.ballots (V, \<F>)) ^ card (rule_voters (svg_sem (V, \<F>)))))"
  have fin_h: "\<forall>v \<in> V. \<bar>?h v\<bar> \<noteq> \<infinity>"
    by simp
  have h_geq_0: "\<forall>v \<in> V. ?h v \<ge> 0"
    by simp
  hence "\<forall>v \<in> V. banzhaf_svg_1 (V, \<F>) v = card (mod.swings svg_swing (V, \<F>) v) / 
    (card (mod.ballots (V, \<F>)) ^ card (rule_voters (svg_sem (V, \<F>))))"
    using banzhaf_rewrite[of V \<F>, OF \<open>(V, \<F>) \<in> S\<close>] card_profiles[of V \<F>, OF \<open>(V, \<F>) \<in> S\<close>] 
          swing_rewrite[of "(V, \<F>)"] mod.swings.simps svg_swings.simps \<open>(V, \<F>) \<in> S\<close>
    by presburger
  hence "\<forall>v \<in> V. banzhaf_svg_1 (V, \<F>) v = ?g v"
    by simp
  moreover have "rule_voters (svg_sem (V, \<F>)) = V"
    by simp
  ultimately have "(\<Sum>v \<in> rule_voters (svg_sem (V, \<F>)). (banzhaf_svg_1 (V, \<F>) v - ?g v)) = 0"
    by simp
  moreover have "\<forall>v \<in> rule_voters (svg_sem (V, \<F>)). \<bar>banzhaf_svg_1 (V, \<F>) v\<bar> \<noteq> \<infinity>"
    using banzhaf_svg_finite
    by metis
  ultimately have "(\<Sum>v \<in> rule_voters (svg_sem (V, \<F>)). (banzhaf_svg_1 (V, \<F>) v)) - 
    (\<Sum>v \<in> rule_voters (svg_sem (V, \<F>)). ?g v) = 0"
    using sum_subtractf_ereal[of "rule_voters (svg_sem (V, \<F>))" "banzhaf_svg_1 (V, \<F>)" ?g]
    by simp
  hence 
    "(\<Sum>v \<in> rule_voters (svg_sem (V, \<F>)). (banzhaf_svg_1 (V, \<F>) v)) =
      (\<Sum>v \<in> rule_voters (svg_sem (V, \<F>)). ?g v)"
    using Infty_neq_0(2,4) ereal_diff_eq_0_iff ereal_diff_eq_MInfty_iff ereal_minus_diff_eq
      ereal_x_minus_x
    by simp
  moreover have "(\<Sum>v\<in>rule_voters (svg_sem (V, \<F>)). ?g v) = 
    (\<Sum>v\<in>rule_voters (svg_sem (V, \<F>)). ?h v) / ?x"
    using sum_div_ereal[of "rule_voters (svg_sem (V, \<F>))" ?h ?x] fin_h h_geq_0
    by simp
  ultimately show
    "mod.power_sum banzhaf_svg_1 (V, \<F>) =
       (\<Sum>v\<in>rule_voters (svg_sem (V, \<F>)). ereal (real (card (mod.swings svg_swing (V, \<F>) v)))) /
       ereal (real (card (mod.ballots (V, \<F>)) ^ card (rule_voters (svg_sem (V, \<F>)))))"
    unfolding mod.power_sum.simps
    by metis
qed

lemma (in simple_voting_game_model) svg_transfer_banzhaf_no_change:
  fixes p :: "('v, 'b) Profile" and r :: 'r and V :: "'v set" and \<F> :: "'v set set" and v :: 'v
  assumes 
    "p \<in> mod.profiles (V, \<F>)" and
    "v \<in> svg_voters (V, \<F>)" and
    "r \<in> svg_results (V, \<F>)" and
    "r = result1 \<Longrightarrow> preimg_in V p {ballot1} \<in> coalitions (V, \<F>)" and
    "r = result2 \<Longrightarrow> preimg_in V p {ballot1} \<notin> coalitions (V, \<F>)"
  shows "banzhaf_svg_1 (result_transform_svg p r (V, \<F>)) v - banzhaf_svg_1 (V, \<F>) v = 0"
proof - 
  have "result_transform_svg p r (V, \<F>) = (V, \<F>)"
    using assms
    by fastforce
  hence "banzhaf_svg_1 (result_transform_svg p r (V, \<F>)) v = banzhaf_svg_1 (V, \<F>) v"
    by metis
  thus ?thesis
    using banzhaf_svg_finite[of V \<F> v]
    by simp
qed

lemma (in simple_voting_game_model) profile_swing_iff_coalition_swing:
  fixes p :: "('v, 'b) Profile" and V :: "'v set" and \<F> :: "'v set set" and v :: 'v
  assumes "p \<in> mod.profiles (V, \<F>)" and "\<forall>v. v \<notin> V \<longrightarrow> p v = ballot2"
  shows "svg_swing (V, \<F>) v p \<longleftrightarrow> (swing_coalition (V, \<F>) v (preimg_in V p {ballot1}))"
proof (safe)
  assume "svg_swing (V, \<F>) v p"
  then obtain C' :: "'v set" where
    swing: "swing_coalition (V, \<F>) v C'" and
    prof: "p = svg_profile (V, \<F>) C'"
    by auto
  hence "p = svg_profile (V, \<F>) (preimg_in V p {ballot1})"
    using assms profile_is_preimg_svg_profile[of p V \<F>]
    by meson
  hence "svg_profile (V, \<F>) C' = svg_profile (V, \<F>) (preimg_in V p {ballot1})"
    using prof
    by metis
  moreover have "mod.voters (V, \<F>) = V"
    by simp
  moreover have "preimg_in V p {ballot1} \<in> Pow V"
    by simp
  moreover have "C' \<subseteq> V"
    using swing
    by simp
  ultimately have "C' = preimg_in V p {ballot1}"
    using inj_on_svg_profile[of "(V, \<F>)"] \<open>C' \<subseteq> V\<close> 
    unfolding inj_on_def
    by simp
  thus "swing_coalition (V, \<F>) v (preimg_in V p {ballot1})"
    using swing
    by metis
next
  assume "swing_coalition (V, \<F>) v (preimg_in V p {ballot1})"
  moreover have "p = svg_profile (V, \<F>) (preimg_in V p {ballot1})"
    using profile_is_preimg_svg_profile[of p V \<F>] assms
    by metis
  ultimately show "svg_swing (V, \<F>) v p"
    unfolding svg_swing.simps svg_swings.simps
    by blast
qed

lemma (in simple_voting_game_model) svg_transfer_banzhaf_change:
  fixes p :: "('v, 'b) Profile" and r :: 'r and V :: "'v set" and \<F> :: "'v set set" and v :: 'v
  assumes 
    "finite V" and
    prof: "p \<in> mod.profiles (V, \<F>)" and
    "v \<in> svg_voters (V, \<F>)" and
    "r \<in> svg_results (V, \<F>)" and
    "r = result1 \<Longrightarrow> preimg_in V p {ballot1} \<notin> coalitions (V, \<F>)" and
    "r = result2 \<Longrightarrow> preimg_in V p {ballot1} \<in> coalitions (V, \<F>)"
  shows
    "banzhaf_svg_1 (result_transform_svg p r (V, \<F>)) v - banzhaf_svg_1 (V, \<F>) v =
      (if svg_swing (V, \<F>) v p then -1 else 1) * 1 / 2^(card V)"
proof (cases "r = result1", split if_splits, safe)
  let ?C = "preimg_in V p {ballot1}"
  let ?G' = "result_transform_svg p r (V, \<F>)"
  have "r = result1 \<Longrightarrow> ?C \<in> coalitions ?G'"
    by simp
  moreover have "r = result2 \<Longrightarrow> ?C \<notin> coalitions ?G'"
    using simple_voting_game_model_axioms
    unfolding simple_voting_game_model_def simple_voting_game_model_axioms_def
    by auto
  ultimately obtain \<F>' :: "'v set set" where 
    rewrite: "?G' = (V, \<F>')" and win_change: "\<not> (?C \<in> \<F> \<longleftrightarrow> ?C \<in> \<F>')"
    using assms simple_voting_game_model_axioms 
    unfolding simple_voting_game_model_def simple_voting_game_model_axioms_def
    by auto
  have "\<forall>C. C \<noteq> ?C \<longrightarrow> (C \<in> \<F> \<union> {?C} \<longleftrightarrow> C \<in> \<F>)"
    by simp
  moreover have "\<forall>C. C \<noteq> ?C \<longrightarrow> (C \<in> \<F> - {?C} \<longleftrightarrow> C \<in> \<F>)"
    by simp
  moreover have \<F>'_def: "\<F>' \<in> {\<F> \<union> {?C}, \<F> - {?C}}"
    using rewrite result_transform_svg.simps[of p r V \<F>]
    unfolding Let_def
    by (metis insert_iff snd_eqD)
  ultimately have eq_other_coalitions: "\<forall>C. C \<noteq> ?C \<longrightarrow> (C \<in> \<F> \<longleftrightarrow> C \<in> \<F>')"
    by blast
  {
    assume "r = result1"
    hence elt: "?C \<in> \<F>'"
      using assms win_change
      by simp
    {
      assume swing: "svg_swing (V, \<F>) v p"
      hence "\<exists>C \<subseteq> V. p = svg_profile (V, \<F>) C"
        unfolding svg_swing.simps svg_swings.simps svg_profile.simps swing_coalition.simps
        by auto
      hence "\<forall>v. v \<notin> V \<longrightarrow> p v = ballot2"
        by auto
      hence neq: "((?C \<union> {v}) \<in> \<F>) \<noteq> ((?C - {v}) \<in> \<F>)"
        using swing profile_swing_iff_coalition_swing[of p V \<F> v, OF prof]
        unfolding svg_swing.simps svg_swings.simps swing_coalition.simps
        by presburger
      moreover have "?C \<in> {?C \<union> {v}, ?C - {v}}"
        by auto
      ultimately have "((?C \<union> {v}) \<in> \<F>') = ((?C - {v}) \<in> \<F>')"
        using win_change \<F>'_def eq_other_coalitions insertE 
        by auto
      hence sw_preimg_\<F>': "swing_vote_svg \<F>' v ?C = 0"
        by simp
      moreover have sw_preimg_\<F>: "swing_vote_svg \<F> v ?C = 1" 
        using neq by simp
      moreover have 
        "banzhaf_svg_1 ?G' v = (1/(2^(card V))) * (\<Sum> S \<in> Pow V. swing_vote_svg \<F>' v S)"
        using assms rewrite 
        by simp
      moreover have 
        "... = (1/(2^(card V))) * (swing_vote_svg \<F>' v (?C \<union> {v}))
          + (1/(2^(card V))) * (swing_vote_svg \<F>' v (?C - {v}))
          + (1/(2^(card V))) * (\<Sum> S \<in> Pow V - {?C \<union> {v}, ?C - {v}}. swing_vote_svg \<F>' v S)"
        sorry
      moreover have 
        "\<forall>S \<in> Pow V - {?C \<union> {v}, ?C - {v}}. swing_vote_svg \<F>' v S = swing_vote_svg \<F> v S"
        using eq_other_coalitions
        sorry
      ultimately have bz': "banzhaf_svg_1 ?G' v = 
        (1/(2^(card V))) * (\<Sum> S \<in> Pow V - {?C \<union> {v}, ?C - {v}}. swing_vote_svg \<F> v S)"
        by simp
      have "banzhaf_svg_1 (V, \<F>) v = (1/(2^(card V))) * (\<Sum> S \<in> Pow V. swing_vote_svg \<F> v S)"
        using assms
        by simp
      also have "... = (1/(2^(card V))) * (swing_vote_svg \<F> v (?C \<union> {v}))
        + (1/(2^(card V))) * (swing_vote_svg \<F> v (?C - {v}))
        + (1/(2^(card V))) * (\<Sum> S \<in> Pow V - {?C \<union> {v}, ?C - {v}}. swing_vote_svg \<F> v S)"
        sorry
      also have "... = (1/(2^(card V))) * 2
        + (1/(2^(card V))) * (\<Sum> S \<in> Pow V - {?C \<union> {v}, ?C - {v}}. swing_vote_svg \<F> v S)"
        using sw_preimg_\<F>'
        sorry
      finally have "banzhaf_svg_1 (V, \<F>) v = (1/(2^(card V))) * 2
        + (1/(2^(card V))) * (\<Sum> S \<in> Pow V - {?C \<union> {v}, ?C - {v}}. swing_vote_svg \<F> v S)"
        by simp
      hence "banzhaf_svg_1 ?G' v - banzhaf_svg_1 (V, \<F>) v = - (1/(2^(card V))) * 2"
        using bz'
        sorry
      thus "banzhaf_svg_1 (result_transform_svg p result1 (V, \<F>)) v - banzhaf_svg_1 (V, \<F>) v 
        = - 1 * 1 / 2 ^ card V"
        sorry
      next
    }
    {
      assume "\<not> svg_swing (V, \<F>) v p"
      thus "banzhaf_svg_1 (result_transform_svg p result1 (V, \<F>)) v - 
        banzhaf_svg_1 (V, \<F>) v = 1 * 1 / 2 ^ card V"
        sorry
    }
  }
  next
    assume "r \<noteq> result1"
    thus "banzhaf_svg_1 (result_transform_svg p r (V, \<F>)) v - banzhaf_svg_1 (V, \<F>) v = 
      (if svg_swing (V, \<F>) v p then - 1 else 1) * 1 / 2 ^ card V"
      sorry
  qed
    
(* TODO with the current formlation, the transfer axiom is satisfied outside of monotone SVGs;
    that good or bad or meh? *)

theorem (in simple_voting_game_model) svg_banzhaf_sat_transfer:
  "svg_tf_axiom.satisfies banzhaf_svg_1"
proof (unfold svg_tf_axiom.satisfies.simps mod.transfer_ax.simps, safe)
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
    res: "r \<in> mod.results (V, \<F>)" and
    eq_V_V': "mod.voters (V, \<F>) = mod.voters (V', \<F>')" and
    eq_B_B': "mod.ballots (V, \<F>) = mod.ballots (V', \<F>')" and
    eq_R_R': "mod.results (V, \<F>) = mod.results (V', \<F>')" and
    eq_res: "\<forall>q \<in> reachability_svg p v. mod.aggregation (V, \<F>) q = mod.aggregation (V', \<F>') q"
  let ?G' = "result_transform_svg p r (V, \<F>)"
  let ?G'' = "result_transform_svg p r (V', \<F>')"
  let ?C = "preimg_in V p {ballot1}"
  have "mod.aggregation (V, \<F>) p = mod.aggregation (V', \<F>') p"
    using eq_res svg_tf_axiom.transfer_axiom_axioms
    unfolding transfer_axiom_def transfer_axiom_axioms_def mod.profile_reachability.simps
    by simp
  moreover have 
    "mod.aggregation (V, \<F>) p = (if (preimg_in V p {ballot1} \<in> \<F>) then result1 else result2)"
    by simp
  moreover have 
    "mod.aggregation (V', \<F>') p = (if (preimg_in V' p {ballot1} \<in> \<F>') then result1 else result2)"
    by simp
  moreover have "preimg_in V' p {ballot1} = ?C"
    using eq_V_V'
    by simp
  moreover have "result1 \<noteq> result2"
    using simple_voting_game_model_axioms
    unfolding simple_voting_game_model_def simple_voting_game_model_axioms_def
    by meson
  ultimately have eq_winning_coalitions: "?C \<in> \<F> \<longleftrightarrow> ?C \<in> \<F>'"
    by metis
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
    with True show ?thesis
    proof (cases "?C \<in> \<F>")
      show ?thesis
        using prof vot res svg_transfer_banzhaf_no_change[of p V \<F> v r]
              svg_transfer_banzhaf_no_change[of p V \<F>' v r]
        sorry
    next
      case False
      hence "?C \<notin> \<F>'"
        using eq_winning_coalitions
        by meson
      
      then show ?thesis sorry
    qed
  next
    case False
    hence "?G' = (V, \<F> - {?C})"
      by simp
    have "?G'' = (V, \<F>' - {?C})"
      using eq_V_V' False
      by simp
    have "r = result2"
      using False res simple_voting_game_model_axioms
      unfolding simple_voting_game_model_def simple_voting_game_model_axioms_def
      by simp
    thus ?thesis
    proof (cases "?C \<in> \<F>")
      case True
      then show ?thesis sorry
    next
      case False
      hence "result_transform_svg p r (V, \<F>) = (V, \<F>)"
        using \<open>r = result2\<close> \<open>result1 \<noteq> result2\<close> 
        by simp
      hence "banzhaf_svg_1 (result_transform_svg p r (V, \<F>)) v = banzhaf_svg_1 (V, \<F>) v"
        by metis
      hence eq_0: "banzhaf_svg_1 (result_transform_svg p r (V, \<F>)) v - banzhaf_svg_1 (V, \<F>) v = 0"
        using banzhaf_svg_finite[of V \<F> v]
        by simp
      from False have "?C \<notin> \<F>'"
        using eq_winning_coalitions
        by blast
      hence "result_transform_svg p r (V', \<F>') = (V', \<F>')" (* TODO proof is repetitive *)
        using \<open>r = result2\<close> \<open>result1 \<noteq> result2\<close> eq_V_V'
        by auto
      hence "banzhaf_svg_1 (result_transform_svg p r (V', \<F>')) v = banzhaf_svg_1 (V', \<F>') v"
        by metis
      hence 
        "banzhaf_svg_1 (result_transform_svg p r (V', \<F>')) v - banzhaf_svg_1 (V', \<F>') v = 0"
        using banzhaf_svg_finite[of V' \<F>' v]
        by simp
      thus ?thesis 
        using eq_0
        by simp
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
    using svg_swings.elims ext
    by (metis (no_types, lifting))
  moreover have "mod.swings svg_swing G v = {p | p. p \<in> mod.profiles G \<and> svg_swing G v p}"
    by simp
  ultimately show "svg_swings G v = mod.swings svg_swing G v"
    using swing_rewrite[of G v]
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

theorem (in finite_simple_voting_game_model) monotone_SVG_banzhaf_sat_axioms: 
  assumes "S \<subseteq> monotone_SVGs"
  shows "svg_banzhaf_index_axioms.is_axm_banzhaf_index banzhaf_svg_1"
  using svg_banzhaf_sat_symmetry svg_banzhaf_sat_null_player
    svg_banzhaf_sat_total_power svg_banzhaf_sat_transfer 
  unfolding svg_banzhaf_index_axioms.is_axm_banzhaf_index.simps 
        svg_banzhaf_index_axioms.vp_axiom.satisfies.simps
        svg_sym_axiom.satisfies.simps svg_np_axiom.satisfies.simps 
        svg_tp_axiom.satisfies.simps svg_tf_axiom.satisfies.simps
  by blast

theorem (in simple_voting_game_model) unique_banzhaf_axioms:
  fixes f :: "'v Simple_Voting_Game \<Rightarrow> 'v \<Rightarrow> ereal"
  shows "svg_banzhaf_index_axioms.vp_axiom.uniqueness_in {\<delta> |\<delta>. (\<forall>G. G \<notin> S \<longrightarrow> \<delta> G = f G)}"
  sorry

text \<open>
  The Banzhaf Index as defined by banzhaf_svg_1 on finite SVGs measures the uniformly distributed
  probability of having a swing vote.
\<close>
  
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
    using banzhaf_rewrite \<open>(V, \<F>) \<in> S\<close>
    by simp
  moreover have "card (Pow V) = card (svg_profile (V, \<F>) ` Pow V)"
  proof -
    have "\<forall>S\<in>Pow V. \<forall>S'\<in>Pow V. S \<noteq> S' \<longrightarrow> (\<exists>v \<in> S. v \<notin> S') \<or> (\<exists>v \<in> S'. v \<notin> S)"
      by blast
    hence "\<forall>S\<in>Pow V. \<forall>S'\<in>Pow V. S \<noteq> S' \<longrightarrow> 
      (\<exists>v. svg_profile (V, \<F>) S v = ballot1 \<and> svg_profile (V, \<F>) S' v = ballot2) \<or> 
      (\<exists>v. svg_profile (V, \<F>) S' v = ballot1 \<and> svg_profile (V, \<F>) S v = ballot2)"
      unfolding svg_profile.simps
      by metis
    hence "\<forall>S\<in>Pow V. \<forall>S'\<in>Pow V. S \<noteq> S' \<longrightarrow> (\<exists>v. svg_profile (V, \<F>) S v \<noteq> svg_profile (V, \<F>) S' v)"
      using finite_simple_voting_game_model_axioms
      unfolding finite_simple_voting_game_model_def simple_voting_game_model_def 
                simple_voting_game_model_axioms_def
      by metis
    hence "inj_on (svg_profile (V, \<F>)) (Pow V)"
      unfolding inj_on_def 
      by metis
    thus ?thesis
      using card_image
      by metis
  qed
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