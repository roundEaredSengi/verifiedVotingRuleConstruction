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

fun aggregation_method :: 
  "'b \<Rightarrow> 'b \<Rightarrow> 'r \<Rightarrow> 'r \<Rightarrow> 'v Simple_Voting_Game \<Rightarrow> (('v \<Rightarrow> 'b) \<Rightarrow> 'r)" where
  "aggregation_method ball1 ball2 res1 res2 (V, \<F>) p = 
    (if (preimg_in V p {ball1} \<in> \<F>) then res1 else res2)"

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
  where "swing_coalition (V, \<F>) v C = (C \<subseteq> V \<and> ((C \<union> {v}) \<in> \<F>) \<noteq> ((C - {v}) \<in> \<F>))"

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
   
(* TODO: make case distinction less repetitive, close "sorry"s *)
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
    coal_p: "p = svg_profile (V, \<F>) C"
    by auto
  hence preimg_p: "preimg_in V p {ballot1} = C"
    sorry
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
    have preimg_q: "preimg_in V ?q {ballot1} = C - {v}"
      using preimg_p True
      sorry
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
    have preimg_q: "preimg_in V ?q {ballot1} = C \<union> {v}"
      using preimg_p False
      sorry
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

sublocale simple_voting_game_model \<subseteq> svg_tf_axiom: 
  transfer_axiom S svg_sem
  "{mod.transfer_ax result_transform_svg reachability_svg}" result_transform_svg reachability_svg
proof (unfold_locales, simp, 
        unfold mod.result_based_transformation.simps mod.profile_reachability.simps, safe)
  fix
    V :: "'v set" and
    \<F> :: "'v set set" and
    p :: "('v, 'b) Profile" and
    r :: 'r
  assume
    "(V, \<F>) \<in> S" and
    "p \<in> mod.profiles (V, \<F>)" and
    "r \<in> mod.results (V, \<F>)"
  (* TODO are the rules equal on UNIV or actually just on profiles (V, \<F>)? 
    (this lead to redefining the transfer axiom's result-transformation requirement) *)
  let ?C = "preimg_in V p {ballot1}"
  let ?svgTransform = "svg_rule ballot1 ballot2 result1 result2 (result_transform_svg p r (V, \<F>))"
  let ?ruleTransform = "rule_transform (svg_rule ballot1 ballot2 result1 result2 (V, \<F>)) p r"
  let ?originalRule = "rule (svg_rule ballot1 ballot2 result1 result2 (V, \<F>))"
  have "result_transform_svg p r (V, \<F>) \<in> {(V, \<F> - {?C}), (V, \<F> \<union> {?C})}"
    unfolding result_transform_svg.simps Let_def If_def
    by auto
  then obtain \<F>' :: "'v set set" where 
    "\<F>' \<in> {\<F> - {?C}, \<F> \<union> {?C}}" and
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
    assume "q \<in> mod.profiles (V, \<F>)"
    let ?f = "aggregation_method ballot1 ballot2 result1 result2 (V, \<F>')"
    let ?f' = "\<lambda>q. (if \<forall>v\<in>V. q v = p v then r else ?originalRule q)"
    show "?f q = ?f' q"
      sorry
  qed
  ultimately show 
    "let (V1, B1, R1, f1) = ?svgTransform; (V2, B2, R2, f2) = ?ruleTransform
       in V1 = V2 \<and> B1 = B2 \<and> R1 = R2 \<and> (\<forall>q\<in>mod.profiles (V, \<F>). f1 q = f2 q)"
    by simp
next
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
    by auto (* TODO why not metis or sth.? *)
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