chapter \<open>Simple Voting Games\<close>

theory Simple_Voting_Game
  imports Voting_Model
          Voting_Power

begin                           

section \<open>Simple Voting Game Definition\<close>

text \<open>
A simple voting game is a tuple consisting of a set (of voters) 
and a set family (of voter coalitions).
\<close>
type_synonym 'v Simple_Voting_Game = "'v set \<times> ('v set set)"

abbreviation coalitions :: "'v Simple_Voting_Game \<Rightarrow> 'v set set" where
  "coalitions G \<equiv> snd G"  

(* use pattern matching instead? *)
(* remove ballot2? *)
(* explain that people who do not vote ballot1 vote ballot2 *)
fun aggregation_method :: 
  "'b \<Rightarrow> 'b \<Rightarrow> 'r \<Rightarrow> 'r \<Rightarrow> 'v Simple_Voting_Game \<Rightarrow> (('v \<Rightarrow> 'b) \<Rightarrow> 'r)" where
  "aggregation_method ballot1 ballot2 result1 result2 (V, \<F>) p = 
    (if (preimg_in V p {ballot1} \<in> \<F>) then result1 else result2)"

definition valid_simple_voting_games :: "'v Simple_Voting_Game set" where
  "valid_simple_voting_games = {G | G. snd G \<subseteq> Pow (fst G)}"

fun monotone_SVG :: "'v Simple_Voting_Game \<Rightarrow> bool" where
  "monotone_SVG (V, \<F>) = (\<forall>S \<in> Pow V. \<forall>T \<in> Pow V. S \<subseteq> T \<longrightarrow> S \<in> \<F> \<longrightarrow> T \<in> \<F>)"

definition monotone_SVGs :: "'v Simple_Voting_Game set" where
  "monotone_SVGs \<equiv> {G | G. G \<in> valid_simple_voting_games \<and> monotone_SVG G}"

definition finite_monotone_SVGs :: "'v Simple_Voting_Game set" where
  "finite_monotone_SVGs \<equiv> {G | G. G \<in> valid_simple_voting_games \<and> finite (fst G) \<and> monotone_SVG G}"

section \<open>Simple Voting Games as a Voting Model\<close> 

fun svg_rule :: 
  "'b \<Rightarrow> 'b \<Rightarrow> 'r \<Rightarrow> 'r \<Rightarrow> ('v Simple_Voting_Game, 'v, 'b, 'r) Voting_Rule_Transformation" where
  "svg_rule b1 b2 r1 r2 (V, \<F>) = (V, {b1, b2}, {r1, r2}, aggregation_method b1 b2 r1 r2 (V, \<F>))"

\<comment> \<open>
  The simple voting game model represents voting systems via objects of type Simple_Voting_Game.
  Simple voting games represent binary decisions on two ballots and two results.
\<close>
locale simple_voting_game_model = 
  mod: voting_model S "svg_rule ballot1 ballot2 result1 result2"
    for S :: "'v Simple_Voting_Game set" and
      ballot1 :: 'b and ballot2 :: 'b and result1 :: 'r and result2 :: 'r +
    assumes "result1 \<noteq> result2" and "ballot1 \<noteq> ballot2" and "\<forall>G \<in> S. snd G \<subseteq> Pow (mod.voters G)"

sublocale simple_voting_game_model \<subseteq> 
  voting_model S "svg_rule ballot1 ballot2 result1 result2"
  by unfold_locales

context simple_voting_game_model
begin

abbreviation "svg_sem \<equiv> svg_rule ballot1 ballot2 result1 result2"

abbreviation "svg_voters \<equiv> rule_voters \<circ> (svg_rule ballot1 ballot2 result1 result2)"
lemma svg_voters_fst [simp]: "svg_voters = fst"
  by auto

abbreviation "svg_ballots \<equiv> rule_ballots \<circ> (svg_rule ballot1 ballot2 result1 result2)"
abbreviation "svg_results \<equiv> rule_results \<circ> (svg_rule ballot1 ballot2 result1 result2)"
abbreviation "svg_aggregation \<equiv> rule \<circ> (svg_rule ballot1 ballot2 result1 result2)"

fun svg_profile :: "'v Simple_Voting_Game \<Rightarrow> 'v set \<Rightarrow> ('v, 'b) Profile" where
  "svg_profile (V, \<F>) X = (\<lambda>v. (if v \<in> X then ballot1 else ballot2))"

end

section \<open>Simple Voting Game Parameters\<close>

fun svg_isomorphism :: "('v \<Rightarrow> 'v) \<Rightarrow> 'v Simple_Voting_Game \<Rightarrow> 'v Simple_Voting_Game" where
  "svg_isomorphism \<pi> (V, \<F>) = (\<pi> ` V, (image \<pi>) ` \<F>)"

fun svg_meet :: "'v Simple_Voting_Game \<Rightarrow> 'v Simple_Voting_Game \<Rightarrow> 'v Simple_Voting_Game" where
  "svg_meet G1 G2 = (fst G1, coalitions G1 \<union> coalitions G2)"

fun (in simple_voting_game_model) svg_join :: 
  "'v Simple_Voting_Game \<Rightarrow> 'v Simple_Voting_Game \<Rightarrow> 'v Simple_Voting_Game" where
  "svg_join G1 G2 = (fst G1, coalitions G1 \<inter> coalitions G2)"

fun (in simple_voting_game_model) swing_coalition :: "'v Simple_Voting_Game \<Rightarrow> 'v \<Rightarrow> 'v set \<Rightarrow> bool"
  where "swing_coalition (V, \<F>) v C = (C \<subseteq> V \<and> v \<in> V \<and> ((C \<union> {v}) \<in> \<F>) \<noteq> ((C - {v}) \<in> \<F>))"

fun (in simple_voting_game_model) svg_swings :: 
  "'v Simple_Voting_Game \<Rightarrow> 'v \<Rightarrow> ('v, 'b) Profile set" where
  "svg_swings (V, \<F>) v = {svg_profile (V, \<F>) X | X. swing_coalition (V, \<F>) v X}"

fun (in simple_voting_game_model) svg_swing :: 
  "'v Simple_Voting_Game \<Rightarrow> 'v \<Rightarrow> ('v, 'b) Profile \<Rightarrow> bool" where
  "svg_swing G v p = (p \<in> svg_swings G v)"

fun (in simple_voting_game_model) \<Phi>_svg :: 
  "('v \<Rightarrow> 'v) \<Rightarrow> 'v Simple_Voting_Game \<Rightarrow> 'v Simple_Voting_Game" where
  "\<Phi>_svg \<sigma> (V, \<F>) = (\<sigma> ` V, {\<sigma> ` C |C. C \<in> \<F>})"

(* If C already maps to r, nothing changes; otherwise add C if r = ballot1 and remove C if r = ballot2 *)
fun (in simple_voting_game_model) result_transform_svg :: 
  "('v, 'b) Profile \<Rightarrow> 'r \<Rightarrow> 'v Simple_Voting_Game \<Rightarrow> 'v Simple_Voting_Game" where
  "result_transform_svg p r (V, \<F>) = (let C = preimg_in V p {ballot1} in 
    (if r = result1 then (V, \<F> \<union> {C}) else (V, \<F> - {C})))"

fun (in simple_voting_game_model) reachability_svg :: 
  "('v, 'b) Profile \<Rightarrow> 'v \<Rightarrow> ('v, 'b) Profile set" where
  "reachability_svg p v = 
    {p, \<lambda>w. (if w = v then (if p v = ballot1 then ballot2 else ballot1) else p w)}"

fun (in simple_voting_game_model) uniform_distr_voters :: 
  "('v Simple_Voting_Game, 'v, ('v, 'b) Profile) Prob_Space" where
  "uniform_distr_voters (V, \<F>) v = uniform_count_measure (svg_profile (V, \<F>) ` Pow V)"

lemma (in simple_voting_game_model) rewrite_profiles:
  fixes V :: "'v set" and \<F> :: "'v set set"
  shows "mod.profiles (V, \<F>) = funcset V {ballot1, ballot2}"
  by simp

lemma (in simple_voting_game_model) svg_profile_is_profile:
  fixes G :: "'v Simple_Voting_Game" and C :: "'v set"
  assumes "C \<subseteq> svg_voters G"
  shows "svg_profile G C \<in> mod.profiles G"
proof -                       
  have "\<forall>v \<in> C. svg_profile G C v = ballot1"
    using assms svg_profile.elims by metis
  moreover have "\<forall>v \<in> (svg_voters G - C). svg_profile G C v = ballot2"
    using svg_profile.elims by (meson DiffD2)
  ultimately have "\<forall>v \<in> svg_voters G. svg_profile G C v \<in> {ballot1, ballot2}"
    by blast
  moreover have "G = (svg_voters G, coalitions G)"
    by simp
  ultimately show ?thesis
    using rewrite_profiles[of "svg_voters G" "coalitions G"]
    by simp
qed

lemma (in simple_voting_game_model) swing_profile_is_swing:
  fixes G :: "'v Simple_Voting_Game" and C :: "'v set" and v :: 'v
  assumes "swing_coalition G v C"
  shows "svg_swing G v (svg_profile G C)"
proof -
  have "G = (svg_voters G, coalitions G)"
    by simp
  hence "svg_profile G C \<in> svg_swings G v"
    unfolding svg_swings.simps
    using assms svg_swings.simps 
    by (metis (mono_tags, lifting) mem_Collect_eq)
  thus ?thesis
    by simp
qed

lemma (in simple_voting_game_model) swing_rewrite:
  fixes G :: "'v Simple_Voting_Game" and v :: 'v
  assumes "G \<in> S"
  shows
    "{svg_profile G C | C. swing_coalition G v C} = {p | p. p \<in> mod.profiles G \<and> svg_swing G v p}"
proof (safe)
  fix C :: "'v set"
  assume swing: "swing_coalition G v C"
  let ?p = "svg_profile G C"
  have "G = (svg_voters G, coalitions G)"
    by simp
  hence "C \<subseteq> svg_voters G"
    using swing swing_coalition.simps[of "svg_voters G" _ v C]
    by metis  
  hence "svg_profile G C = ?p \<and> ?p \<in> mod.profiles G \<and> svg_swing G v ?p"
    using svg_profile_is_profile[of C G] swing_profile_is_swing[of G v C, OF swing]
    by metis
  thus "\<exists>p. svg_profile G C = p \<and> p \<in> mod.profiles G \<and> svg_swing G v p"
    by metis
next
  fix p :: "('v, 'b) Profile"
  assume 
    "p \<in> mod.profiles G" and
    "svg_swing G v p"
  hence "p \<in> {svg_profile G C | C. swing_coalition G v C}"
    unfolding svg_swing.simps
    using svg_swings.simps[of "svg_voters G" "coalitions G" v]
    by simp
  thus "\<exists>C. p = svg_profile G C \<and> swing_coalition G v C"
    by blast
qed

lemma (in simple_voting_game_model) coalition_is_svg_profile_preimg:
  fixes C :: "'v set" and G :: "'v Simple_Voting_Game"
  assumes "C \<subseteq> svg_voters G"
  shows
    "C = preimg_in (svg_voters G) (svg_profile G C) {ballot1}"
proof -
  have "\<forall>v \<in> C. svg_profile G C v = ballot1"
    using svg_profile.elims 
    by metis
  hence subset: "C \<subseteq> preimg_in (svg_voters G) (svg_profile G C) {ballot1}"
    unfolding preimg_in.simps
    using assms by blast
  have "\<forall>v \<in> svg_voters G. v \<notin> C \<longrightarrow> svg_profile G C v = ballot2"
    using svg_profile.elims 
    by metis
  hence "\<forall>v \<in> svg_voters G. svg_profile G C v = ballot1 \<longrightarrow> v \<in> C"
    using simple_voting_game_model_axioms
    unfolding simple_voting_game_model_def simple_voting_game_model_axioms_def
    by metis
  hence "preimg_in (svg_voters G) (svg_profile G C) {ballot1} \<subseteq> C"
    unfolding preimg_in.simps
    by blast
  thus ?thesis
    using subset
    by simp
qed 

lemma (in simple_voting_game_model) profile_is_preimg_svg_profile:
  fixes p :: "('v, 'b) Profile" and V :: "'v set" and \<F> :: "'v set set"
  assumes "p \<in> mod.profiles (V, \<F>)" and "\<forall>v. v \<notin> V \<longrightarrow> p v = ballot2"
  shows "p = svg_profile (V, \<F>) (preimg_in V p {ballot1})"
proof -
  have "\<forall>v \<in> V. p v \<in> {ballot1, ballot2}"
    using assms simple_voting_game_model_axioms
    unfolding simple_voting_game_model_def simple_voting_game_model_axioms_def voting_model_def
              rule_profiles.simps Pi_def
    by simp
  hence "\<forall>v \<in> V. p v \<noteq> ballot1 \<longleftrightarrow> p v = ballot2"
    using simple_voting_game_model_axioms
    unfolding simple_voting_game_model_def simple_voting_game_model_axioms_def voting_model_def
    by blast
  hence "\<forall>v \<in> V. v \<notin> preimg_in V p {ballot1} \<longleftrightarrow> p v = ballot2"
    by simp
  moreover have "\<forall>v \<in> V. v \<in> preimg_in V p {ballot1} \<longleftrightarrow> p v = ballot1"
    by simp
  ultimately have eq_on_V: "\<forall>v \<in> V. p v = svg_profile (V, \<F>) (preimg_in V p {ballot1}) v"
    using assms
    by simp
  have "\<forall>v. v \<notin> V \<longrightarrow> svg_profile (V, \<F>) (preimg_in V p {ballot1}) v = ballot2"
    by simp
  hence "\<forall>v. v \<notin> V \<longrightarrow> p v = svg_profile (V, \<F>) (preimg_in V p {ballot1}) v"
    using assms
    by simp
  thus ?thesis
    using eq_on_V
    by blast
qed

lemma (in simple_voting_game_model) inj_on_svg_profile:
  fixes G :: "'v Simple_Voting_Game" and v :: 'v
  shows "inj_on (svg_profile G) (Pow (svg_voters G))" 
proof (unfold inj_on_def, clarify)
  fix C :: "'v set" and D :: "'v set"
  assume "C \<subseteq> svg_voters G" and "D \<subseteq> svg_voters G" and "svg_profile G C = svg_profile G D"
  thus "C = D"
    using coalition_is_svg_profile_preimg[of C G] coalition_is_svg_profile_preimg[of D G]
    by metis
qed

lemma (in simple_voting_game_model) swing_cardinality:
  fixes V :: "'v set" and \<F> :: "'v set set" and v :: 'v
  shows 
    "card (svg_swings (V, \<F>) v) = card {C | C. swing_coalition (V, \<F>) v C}"
proof -
  let ?f = "svg_profile (V, \<F>)"
  let ?swing_coalitions = "{C | C. swing_coalition (V, \<F>) v C}"
  have "?swing_coalitions \<subseteq> Pow V"
    by (simp add: Collect_mono_iff Pow_def)
  hence "inj_on ?f ?swing_coalitions"
    using inj_on_svg_profile[of "(V, \<F>)"] svg_voters_fst 
    by (metis fstI inj_on_subset)
  moreover have "?f ` ?swing_coalitions = svg_swings (V, \<F>) v"
    using Setcompr_eq_image[of ?f ?swing_coalitions]
    by simp
  ultimately show ?thesis
    by (metis card_image)
qed

section \<open>Simple Voting Game Voting Power\<close>

lemma preimg_helper: 
  fixes
    f :: "'x \<Rightarrow> 'y" and
    X :: "'x set" and 
    y :: 'y and
    \<F> :: "'x set set" and 
    \<sigma> :: "'x \<Rightarrow> 'x"
  shows
    "preimg_in (\<sigma> ` X) f {y} = \<sigma> ` (preimg_in X (f \<circ> \<sigma>) {y})"
proof (safe)
  fix x :: 'x
  assume x_preimg: "x \<in> preimg_in (\<sigma> ` X) f {y}"
  moreover have "preimg_in (\<sigma> ` X) f {y} \<subseteq> \<sigma> ` X"
    by simp
  ultimately have "x \<in> \<sigma> ` X"
    by simp
  then obtain x' :: 'x where "x' \<in> X" and "\<sigma> x' = x"
    unfolding image_def
    by blast
  moreover with this have "f (\<sigma> x') = y"
    using x_preimg
    by simp
  ultimately have "x' \<in> preimg_in X (f \<circ> \<sigma>) {y}"
    by simp
  thus "x \<in> \<sigma> ` (preimg_in X (f \<circ> \<sigma>) {y})"
    using \<open>\<sigma> x' = x\<close>
    by blast
next
  fix x :: 'x
  assume x_preimg: "x \<in> preimg_in X (f \<circ> \<sigma>) {y}"
  hence "x \<in> X"
    by simp
  hence "\<sigma> x \<in> \<sigma> ` X"
    by simp
  moreover have "f (\<sigma> x) = y"
    using x_preimg
    by simp
  ultimately show "\<sigma> x \<in> preimg_in (\<sigma> ` X) f {y}"
    by simp
qed

lemma bij_preimg: 
  fixes 
    X :: "'x set" and
    Y :: "'x set" and
    \<sigma> :: "'x \<Rightarrow> 'x" and
    \<F> :: "'x set set"
  assumes "bij \<sigma>"
  shows 
    "\<sigma> ` X = Y \<longleftrightarrow> X = the_inv \<sigma> ` Y"
proof (safe)
  fix x :: 'x
  assume "Y = \<sigma> ` X" and "x \<in> X"
  moreover have "the_inv \<sigma> ` \<sigma> ` X = X"
    using assms
    by (metis bij_betw_def image_vimage_eq inj_on_the_inv_into 
          inj_vimage_image_eq the_inv_into_vimage top_greatest)
  ultimately show "x \<in> the_inv \<sigma> ` \<sigma> ` X"
    by metis
next
  fix x :: 'x
  assume "x \<in> X"
  moreover have "the_inv \<sigma> (\<sigma> x) = x"
    using assms
    by (simp add: bij_betw_def the_inv_f_f)
  ultimately show "the_inv \<sigma> (\<sigma> x) \<in> X"
    by simp
next
  fix y :: 'x
  assume "y \<in> Y"
  moreover have "\<sigma> (the_inv \<sigma> y) = y"
    using assms
    by (simp add: f_the_inv_into_f_bij_betw)
  ultimately show "\<sigma> (the_inv \<sigma> y) \<in> Y"
    by simp
next
  fix y :: 'x
  assume "y \<in> Y"
  moreover have "\<sigma> ` the_inv \<sigma> ` Y = Y"
    using assms
    by (metis bij_betw_def inf_top.right_neutral inj_on_the_inv_into
          inj_vimage_image_eq the_inv_into_vimage top_greatest)
  ultimately show "y \<in> \<sigma> ` the_inv \<sigma> ` Y"
    by metis
qed

lemma bij_img_containment:
    fixes 
    X :: "'x set" and
    \<sigma> :: "'x \<Rightarrow> 'x" and
    \<F> :: "'x set set"
  assumes "bij \<sigma>"
  shows "X \<in> \<F> \<longleftrightarrow> \<sigma> ` X \<in> {\<sigma> ` Z |Z. Z \<in> \<F>}"
proof (safe)
next
  assume "X \<in> \<F>"
  thus "\<exists>Z. \<sigma> ` X = \<sigma> ` Z \<and> Z \<in> \<F>"
    by metis
next
  fix Z :: "'x set"
  assume "\<sigma> ` X = \<sigma> ` Z" and "Z \<in> \<F>"
  moreover with this have "X = Z"
    using assms bij_preimg
    by metis
  ultimately show "X \<in> \<F>"
    by metis
qed
   
theorem (in simple_voting_game_model) svg_swing_is_predicate:
  "mod.swing_vote_predicate svg_swing"
proof (simp, safe)
  fix V :: "'v set" and \<F> :: "'v set set" and v :: 'v and p :: "('v, 'b) Profile"
  assume 
    valid: "(V, \<F>) \<in> S" and 
    vot_v: "v \<in> mod.voters (V, \<F>)" and 
    valid_prof: "p \<in> mod.voters (V, \<F>) \<rightarrow> mod.ballots (V, \<F>)" and
    swing: "p \<in> svg_swings (V, \<F>) v"
  then obtain C :: "'v set" where 
    coal_p: "p = svg_profile (V, \<F>) C" and "C \<subseteq> V"
    by auto
  hence preimg_p: "preimg_in V p {ballot1} = C"
    using coalition_is_svg_profile_preimg[of C "(V, \<F>)"]
    by simp
  let ?thesis = 
    "\<exists>q \<in> mod.voters (V, \<F>) \<rightarrow> mod.ballots (V, \<F>).
          p v \<noteq> q v \<and> mod.aggregation (V, \<F>) p \<noteq> mod.aggregation (V, \<F>) q"
  show ?thesis
  proof (cases "p v = ballot1")
    case True
    hence "v \<in> C"
      using coal_p
      unfolding svg_profile.simps
      by (metis simple_voting_game_model_axioms_def simple_voting_game_model_def
          simple_voting_game_model_axioms)
    hence "C = C \<union> {v}"
      by auto
    moreover have "\<forall>C' \<subseteq> V. C' \<noteq> C \<longrightarrow> p \<noteq> svg_profile (V, \<F>) C'"
      using coal_p
      unfolding svg_profile.simps
      by (metis simple_voting_game_model_axioms_def simple_voting_game_model_def 
          subsetI subset_antisym simple_voting_game_model_axioms)
    moreover have "\<exists>C' \<subseteq> V. p = svg_profile (V, \<F>) C' \<and> (C' \<union> {v} \<in> \<F>) \<noteq> (C' - {v} \<in> \<F>)"
      using swing
      by auto
    ultimately have swing_minus_v: "(C \<in> \<F>) \<noteq> (C - {v} \<in> \<F>)"
      using swing coal_p
      by metis
    let ?q = "svg_profile (V, \<F>) (C - {v})"
    have "C - {v} \<subseteq> V"
      using \<open>C \<subseteq> V\<close>
      by blast
    moreover have "(rule_voters \<circ> svg_sem) (V, \<F>) = V"
      by simp
    ultimately have preimg_q: "preimg_in V ?q {ballot1} = C - {v}"
      using coalition_is_svg_profile_preimg[of "C - {v}" "(V, \<F>)"]
      by metis
    have neq: "?q v = ballot2"
      by simp
    have "mod.aggregation (V, \<F>) p = rule (svg_rule ballot1 ballot2 result1 result2 (V, \<F>)) p"
      by simp
    moreover have 
      "mod.aggregation (V, \<F>) ?q = rule (svg_rule ballot1 ballot2 result1 result2 (V, \<F>)) ?q"
      by simp
    moreover have 
      "(if C \<in> \<F> then result1 else result2) \<noteq> (if C - {v} \<in> \<F> then result1 else result2)"
      using swing_minus_v
      by (metis simple_voting_game_model_axioms_def simple_voting_game_model_def
          simple_voting_game_model_axioms)
    moreover with this have 
      "rule (svg_rule ballot1 ballot2 result1 result2 (V, \<F>)) p \<noteq> 
        rule (svg_rule ballot1 ballot2 result1 result2 (V, \<F>)) ?q"
      using preimg_p preimg_q
      unfolding svg_rule.simps aggregation_method.simps
      by simp
    ultimately have "mod.aggregation (V, \<F>) p \<noteq> mod.aggregation (V, \<F>) ?q"
      by satx
    moreover have "?q \<in> mod.voters (V, \<F>) \<rightarrow> mod.ballots (V, \<F>)"
      by simp
    moreover have "p v \<noteq> ?q v"
      using neq True
      by (metis simple_voting_game_model_axioms_def simple_voting_game_model_def
          simple_voting_game_model_axioms)
    ultimately show ?thesis by metis
  next
    case False
    moreover have "p v \<in> {ballot1, ballot2}"
      using valid_prof
      unfolding Pi_def
      by (metis coal_p insertCI svg_profile.simps)
    ultimately have "p v = ballot2"
      by simp
    hence "v \<notin> C"
      using coal_p
      unfolding svg_profile.simps
      by (metis simple_voting_game_model_axioms_def simple_voting_game_model_def
          simple_voting_game_model_axioms)
    hence "C = C - {v}"
      by auto
    moreover have "\<forall>C' \<subseteq> V. C' \<noteq> C \<longrightarrow> p \<noteq> svg_profile (V, \<F>) C'"
      using coal_p
      unfolding svg_profile.simps
      by (metis simple_voting_game_model_axioms_def simple_voting_game_model_def 
          subsetI subset_antisym simple_voting_game_model_axioms)
    moreover have "\<exists>C' \<subseteq> V. p = svg_profile (V, \<F>) C' \<and> (C' \<union> {v} \<in> \<F>) \<noteq> (C' - {v} \<in> \<F>)"
      using swing
      by auto
    ultimately have swing_plus_v: "(C \<union> {v} \<in> \<F>) \<noteq> (C \<in> \<F>)"
      using swing coal_p
      by metis
    let ?q = "svg_profile (V, \<F>) (C \<union> {v})"
    have "C \<union> {v} \<subseteq> V"
      using \<open>C \<subseteq> V\<close> vot_v
      by simp
    moreover have "(rule_voters \<circ> svg_sem) (V, \<F>) = V"
      by simp
    ultimately have preimg_q: "preimg_in V ?q {ballot1} = C \<union> {v}"
      using coalition_is_svg_profile_preimg[of "C \<union> {v}" "(V, \<F>)"]
      by metis
    have neq: "?q v = ballot1"
      by simp
        have "mod.aggregation (V, \<F>) p = rule (svg_rule ballot1 ballot2 result1 result2 (V, \<F>)) p"
      by simp
    moreover have 
      "mod.aggregation (V, \<F>) ?q = rule (svg_rule ballot1 ballot2 result1 result2 (V, \<F>)) ?q"
      by simp
    moreover have 
      "(if C \<union> {v} \<in> \<F> then result1 else result2) \<noteq> (if C \<in> \<F> then result1 else result2)"
      using swing_plus_v
      by (metis simple_voting_game_model_axioms_def simple_voting_game_model_def
          simple_voting_game_model_axioms)
    moreover with this have 
      "rule (svg_rule ballot1 ballot2 result1 result2 (V, \<F>)) p \<noteq> 
        rule (svg_rule ballot1 ballot2 result1 result2 (V, \<F>)) ?q"
      using preimg_p preimg_q
      unfolding svg_rule.simps aggregation_method.simps
      by simp
    ultimately have "mod.aggregation (V, \<F>) p \<noteq> mod.aggregation (V, \<F>) ?q"
      by satx
    moreover have "?q \<in> mod.voters (V, \<F>) \<rightarrow> mod.ballots (V, \<F>)"
      by simp
    moreover have "p v \<noteq> ?q v"
      using neq False
      by metis
    ultimately show ?thesis by metis
  qed
qed
 
theorem (in simple_voting_game_model) svg_transform_is_transform:
  "mod.voter_renaming_transformation \<Phi>_svg"
proof (simp, safe)
  fix
    V :: "'v set" and \<F> :: "'v set set" and \<sigma> :: "'v \<Rightarrow> 'v"
  assume "(V, \<F>) \<in> S" and "bij \<sigma>" and "\<Phi>_svg \<sigma> (V, \<F>) \<in> S"
  have "svg_rule ballot1 ballot2 result1 result2 (\<Phi>_svg \<sigma> (V, \<F>)) =
    (\<sigma> ` V, {ballot1, ballot2}, {result1, result2}, 
      aggregation_method ballot1 ballot2 result1 result2 (\<sigma> ` V, {\<sigma> ` C |C. C \<in> \<F>}))"
    by simp
  moreover have "V = mod.voters (V, \<F>)"
    by simp
  moreover have "{ballot1, ballot2} = mod.ballots (V, \<F>)"
    by simp
  moreover have "{result1, result2} = mod.results (V, \<F>)"
    by simp
  moreover have 
    "aggregation_method ballot1 ballot2 result1 result2 (\<sigma> ` V, {\<sigma> ` C |C. C \<in> \<F>})
      = rename_aggregation (mod.aggregation (V, \<F>)) \<sigma>"
  proof
    fix p :: "('v, 'b) Profile"
    have "aggregation_method ballot1 ballot2 result1 result2 (\<sigma> ` V, {\<sigma> ` C |C. C \<in> \<F>}) p
      = (if (preimg_in (\<sigma> ` V) p {ballot1} \<in> {\<sigma> ` C |C. C \<in> \<F>}) then result1 else result2)"
      by simp
    also have "... = (if (preimg_in V (p \<circ> \<sigma>) {ballot1} \<in> \<F>) then result1 else result2)"
      using preimg_helper[of \<sigma> V p ballot1] bij_img_containment[OF \<open>bij \<sigma>\<close>]
      by presburger
    also have "... = rename_aggregation (mod.aggregation (V, \<F>)) \<sigma> p"
      by simp
    finally show 
      "aggregation_method ballot1 ballot2 result1 result2 (\<sigma> ` V, {\<sigma> ` C |C. C \<in> \<F>}) p
        = rename_aggregation (mod.aggregation (V, \<F>)) \<sigma> p"
      by simp
  qed
  ultimately show
    "svg_rule ballot1 ballot2 result1 result2 (\<Phi>_svg \<sigma> (V, \<F>)) =
      (\<sigma> ` mod.voters (V, \<F>), mod.ballots (V, \<F>), mod.results (V, \<F>),
        rename_aggregation (mod.aggregation (V, \<F>)) \<sigma>)"
    by metis
qed

section \<open>Simple Voting Game Axiom Instantiation\<close>

(* TODO 
Claude told me this sublocale thing is better than using interpretations since 
interpretations are forgotten after closing the current locale context; 
document this or is this clear? 
*)
sublocale
  simple_voting_game_model \<subseteq> svg_np_axiom: 
  null_player_axiom S svg_sem "{mod.null_player_ax svg_swing}" svg_swing
  by (unfold_locales, simp, rule local.svg_swing_is_predicate)

sublocale simple_voting_game_model \<subseteq> svg_sym_axiom: 
  symmetry_axiom S svg_sem "{mod.symmetry_ax \<Phi>_svg}" \<Phi>_svg
  by (unfold_locales, simp, rule svg_transform_is_transform)

sublocale simple_voting_game_model \<subseteq> svg_tp_axiom: 
  total_power_axiom S svg_sem "{mod.total_power_ax svg_swing}" svg_swing
  by (unfold_locales, simp, rule local.svg_swing_is_predicate)

lemma (in simple_voting_game_model) result_transform_svg_is_result_transform:
  "mod.result_based_transformation result_transform_svg"
proof (unfold mod.result_based_transformation.simps, safe)
  fix
    V :: "'v set" and
    \<F> :: "'v set set" and
    p :: "('v, 'b) Profile" and
    r :: 'r
  assume
    "(V, \<F>) \<in> S" and
    prof_p: "p \<in> mod.profiles (V, \<F>)" and
    res: "r \<in> mod.results (V, \<F>)"
  (* TODO are the rules equal on UNIV or actually just on profiles (V, \<F>)? 
    (this lead to redefining the transfer axiom's result-transformation requirement) *)
  let ?C = "preimg_in V p {ballot1}"
  let ?svgTransform = "svg_sem (result_transform_svg p r (V, \<F>))"
  let ?ruleTransform = "rule_transform (svg_sem (V, \<F>)) p r"
  let ?originalRule = "rule (svg_sem (V, \<F>))"
  have "result_transform_svg p r (V, \<F>) \<in> {(V, \<F> - {?C}), (V, \<F> \<union> {?C})}"
    unfolding result_transform_svg.simps Let_def If_def
    by auto
  then obtain \<F>' :: "'v set set" where 
    \<F>'_def: "\<F>' \<in> {\<F> - {?C}, \<F> \<union> {?C}}" and
    transform: "result_transform_svg p r (V, \<F>) = (V, \<F>')"
    by blast
  hence 
    "?svgTransform = (V, {ballot1, ballot2}, {result1, result2}, 
      aggregation_method ballot1 ballot2 result1 result2 (V, \<F>'))"
    by simp
  moreover have 
    "?ruleTransform = (V, {ballot1, ballot2}, {result1, result2}, 
      (\<lambda>q. if (\<forall>v \<in> V. q v = p v) then r else ?originalRule q))"
    by auto
  moreover have "\<forall>q \<in> mod.profiles (V, \<F>). 
    aggregation_method ballot1 ballot2 result1 result2 (V, \<F>') q = 
      (\<lambda>q. if (\<forall>v \<in> V. q v = p v) then r else ?originalRule q) q"
  proof (safe)
    fix q :: "('v, 'b) Profile"
    assume prof_q: "q \<in> mod.profiles (V, \<F>)"
    let ?f = "aggregation_method ballot1 ballot2 result1 result2 (V, \<F>')"
    let ?f' = "\<lambda>q. (if \<forall>v\<in>V. q v = p v then r else ?originalRule q)"
    have "r = result1 \<longrightarrow> \<F>' = \<F> \<union> {preimg_in V p {ballot1}}"
      using transform
      unfolding result_transform_svg.simps Let_def
      by auto
    moreover have "r = result2 \<longrightarrow> \<F>' = \<F> - {preimg_in V p {ballot1}}"
      using transform simple_voting_game_model_axioms
      unfolding result_transform_svg.simps Let_def
      by (metis simple_voting_game_model_axioms_def simple_voting_game_model_def split_pairs2)
    ultimately have "(preimg_in V p {ballot1} \<in> \<F>') \<longleftrightarrow> (r = result1)"
      using res
      by auto
    hence "?f p = r"
      using res
      unfolding aggregation_method.simps
      by auto
    moreover have "(\<forall>v\<in>V. q v = p v) \<Longrightarrow> preimg_in V p {ballot1} = preimg_in V q {ballot1}"
      by auto
    ultimately have "(\<forall>v\<in>V. q v = p v) \<Longrightarrow> ?f q = r"
      by simp
    hence eq_prof_coinc: "(\<forall>v\<in>V. q v = p v) \<Longrightarrow> ?f q = ?f' q"
      by simp
    have "\<forall>v \<in> V. p v = ballot1 \<or> p v = ballot2"
      using prof_p rewrite_profiles[of V \<F>]
      unfolding Pi_def
      by simp
    moreover have "\<forall>v \<in> V. q v = ballot1 \<or> q v = ballot2"
      using prof_q rewrite_profiles[of V \<F>]
      unfolding Pi_def
      by simp
    ultimately have "(\<exists>v\<in>V. q v \<noteq> p v) \<Longrightarrow> preimg_in V p {ballot1} \<noteq> preimg_in V q {ballot1}"
      unfolding preimg_in.simps
      by fast
    hence "(\<exists>v\<in>V. q v \<noteq> p v) \<Longrightarrow> preimg_in V q {ballot1} \<in> \<F> \<longleftrightarrow> preimg_in V q {ballot1} \<in> \<F>'"
      using transform \<F>'_def
      unfolding result_transform_svg.simps
      by blast
    hence "(\<exists>v\<in>V. q v \<noteq> p v) \<Longrightarrow> ?f q = ?originalRule q"
      by simp
    thus "?f q = ?f' q"
      using eq_prof_coinc
      by metis
  qed
  ultimately show 
    "let (V1, B1, R1, f1) = ?svgTransform; (V2, B2, R2, f2) = ?ruleTransform
       in V1 = V2 \<and> B1 = B2 \<and> R1 = R2 \<and> (\<forall>q\<in>mod.profiles (V, \<F>). f1 q = f2 q)"
    by simp
qed

sublocale simple_voting_game_model \<subseteq> svg_tf_axiom: 
  transfer_axiom S svg_sem
  "{mod.transfer_ax result_transform_svg reachability_svg}" result_transform_svg reachability_svg
proof (unfold_locales, safe, rule result_transform_svg_is_result_transform, 
        unfold mod.profile_reachability.simps, safe)
  fix
    V :: "'v set" and
    \<F> :: "'v set set" and
    p :: "('v, 'b) Profile" and
    v :: 'v
  assume
    "(V, \<F>) \<in> S" and
    "p \<in> mod.profiles (V, \<F>)" and
    "v \<in> rule_voters (svg_sem (V, \<F>))"
  thus "p \<in> reachability_svg p v"
    by simp
next
  fix
    V :: "'v set" and
    \<F> :: "'v set set" and
    p :: "('v, 'b) Profile" and
    q :: "('v, 'b) Profile" and
    v :: 'v
  assume
    "(V, \<F>) \<in> S" and
    "p \<in> mod.profiles (V, \<F>)" and
    "v \<in> mod.voters (V, \<F>)" and
    "q \<in> reachability_svg p v"
  thus "q \<in> mod.profiles (V, \<F>)"
    by fastforce (* TODO *)
qed

section \<open>Simple Voting Game Interpretations\<close>

text \<open>
  Simple voting games model yes-no-decisions: 
  Voters choose one out of True (= yes) and False (= no) and the result is True (= yes) iff
  a winning coalition of voters chose yes, otherwise the result is False (= no).
\<close>
interpretation boolean_svg:
  simple_voting_game_model valid_simple_voting_games True False True False
proof (unfold_locales, simp_all, safe)
  fix V :: "'a set" and \<F> :: "'a set set" and p :: "('a, bool) Profile"
  assume "p \<in> rule_voters (svg_rule True False True False (V, \<F>)) 
                \<rightarrow> rule_ballots (svg_rule True False True False (V, \<F>))"
  hence "rule (svg_rule True False True False (V, \<F>)) p \<in> {True, False}"
    by simp
  thus "rule (svg_rule True False True False (V, \<F>)) p
          \<in> rule_results (svg_rule True False True False (V, \<F>))"
    by simp
next
  fix V :: "'a set" and \<F> :: "'a set set" and X :: "'a set" and v :: 'a
  assume "(V, \<F>) \<in> valid_simple_voting_games" and "X \<in> coalitions (V, \<F>)" and "v \<in> X"
  thus "v \<in> rule_voters (svg_rule True False True False (V, \<F>))"
    unfolding valid_simple_voting_games_def
    by auto
qed

text \<open>
  We instantiate the I-Power axiom using the uniform distribution on coalitions in games with 
  finite voter sets. To assume finite voter sets, we introduce the corresponding sublocale of 
  the simple_voting_game_model.
\<close>

locale finite_simple_voting_game_model = simple_voting_game_model S ballot1 ballot2 result1 result2
  for S :: "'v Simple_Voting_Game set" and ballot1 :: 'b and ballot2 and result1 :: 'r and result2 +
  assumes 
    finite_voters: "\<forall>G \<in> S. finite (svg_voters G)"

sublocale finite_simple_voting_game_model \<subseteq> simple_voting_game_model
  by unfold_locales

sublocale finite_simple_voting_game_model \<subseteq> svg_ipow_axiom: 
  ipower_axiom S svg_sem "{mod.is_ipower uniform_distr_voters svg_swings}" 
    uniform_distr_voters svg_swings
proof (unfold_locales, metis, safe)
  fix V :: "'v set" and \<F> :: "'v set set" and v :: 'v
  assume
    "(V, \<F>) \<in> S" and "v \<in> rule_voters (svg_sem (V, \<F>))"
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
  moreover with this have 
    "emeasure (uniform_distr_voters (V, \<F>) v) (svg_profile (V, \<F>) ` Pow V) = 1"
    using emeasure_uniform_count_measure[
            of "svg_profile (V, \<F>) ` Pow V" "svg_profile (V, \<F>) ` Pow V"]
    unfolding uniform_distr_voters.simps
    by auto
  ultimately show "prob_space (uniform_distr_voters (V, \<F>) v)"
    using prob_spaceI                    
    by metis
  have "svg_swings (V, \<F>) v \<subseteq> svg_profile (V, \<F>) ` Pow V"
    unfolding svg_swings.simps swing_coalition.simps
    by blast
  thus "svg_swings (V, \<F>) v \<in> sets (uniform_distr_voters (V, \<F>) v)"
    unfolding uniform_distr_voters.simps
    using sets_uniform_count_measure[of "svg_profile (V, \<F>) ` Pow V"]
    by simp
qed

end