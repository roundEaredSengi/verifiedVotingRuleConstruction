theory Ad_Hoc_Definition_Dump
  imports "HOL-Library.Extended_Nonnegative_Real"
          "HOL-Probability.Probability_Measure"
          "../Voting_Models/Voting_Model_Scratch"

begin

section \<open>Basic Definitions and Types\<close>

type_synonym ('v, 'b, 'r) Tallying_Method = "(('v \<Rightarrow> 'b) \<Rightarrow> 'r)" (*TODO*)
type_synonym 'x Voters = "'x set" (*TODO*)

text \<open>
A voting rule is a tuple consisting of three sets (of voters, ballots and outcomes)
and a map (the tallying method).
\<close>
(* TODO 'r set-valued? *)
type_synonym ('v, 'b, 'r) Voting_Rule = "'v Voters \<times> 'b set \<times> 'r set \<times> ('v, 'b, 'r) Tallying_Method"

abbreviation rule :: "('v, 'b, 'r) Voting_Rule \<Rightarrow> ('v, 'b, 'r) Tallying_Method" where
  "rule X \<equiv> snd (snd (snd X))"

abbreviation voters :: "('v, 'b, 'r) Voting_Rule \<Rightarrow> 'v set" where
  "voters X \<equiv> fst X"

abbreviation ballots :: "('v, 'b, 'r) Voting_Rule \<Rightarrow> 'b set" where
  "ballots X \<equiv> fst (snd X)"

abbreviation results :: "('v, 'b, 'r) Voting_Rule \<Rightarrow> 'r set" where
  "results X \<equiv> fst (snd (snd X))"

text \<open>
A strategic game is a tuple consisting of two sets (of voters and outcomes),
a vector of sets (of strategies per voters), a vector of relations 
(one preference relation over outcomes per voter) and a map (the tallying method).
\<close>
type_synonym ('v, 'a, 'r) Strategic_Game = 
  "'v set \<times> 'r set \<times> ('v \<Rightarrow> 'a set) \<times> ('v \<Rightarrow> 'r rel) \<times> (('v \<Rightarrow> 'a) \<Rightarrow> 'r)"

abbreviation voters_strat :: "('v, 'a, 'r) Strategic_Game \<Rightarrow> 'v set" where
  "voters_strat G \<equiv> fst G"

text \<open>
A solution concept is a set of ideal, according to some optimality conditions,
strategy profiles to be chosen by players in a strategic game.
\<close>
type_synonym ('v, 'a, 'r) Solution_Concept =
  "('v, 'a, 'r) Strategic_Game \<Rightarrow> ('v \<Rightarrow> 'a) set"

fun strat_rule :: "('v, 'a, 'r) Strategic_Game \<Rightarrow> ('v, 'a, 'r) Voting_Rule" where
  "strat_rule (V, R, \<A>, \<P>, f) = (V, \<Union>(\<A> ` V), R, f)"

abbreviation outcome_map ::  "('v, 'a, 'r) Strategic_Game \<Rightarrow> (('v \<Rightarrow> 'a) \<Rightarrow> 'r)" where
  "outcome_map G \<equiv> snd (snd (snd (snd G)))"

abbreviation preferences ::  "('v, 'a, 'r) Strategic_Game \<Rightarrow> ('v \<Rightarrow> 'r rel)" where
  "preferences G \<equiv> fst (snd (snd (snd G)))"

type_synonym ('x, 'v) Voting_Power = "'x \<Rightarrow> 'v \<Rightarrow> ereal"
type_synonym ('x, 'v) Voting_Power_Axiom = "'x set \<Rightarrow> ('x, 'v) Voting_Power \<Rightarrow> bool"

section \<open>Auxiliary Definitions and Lemmas\<close>

fun preimg_in :: "'x set \<Rightarrow> ('x \<Rightarrow> 'y) \<Rightarrow> 'y set \<Rightarrow> 'x set" where
  "preimg_in X f Y = {x |x. x \<in> X \<and> f x \<in> Y}"

(* TODO PiE (FuncSet) instead of actual_funcset *)
fun actual_funcset :: "'x set \<Rightarrow> 'y set \<Rightarrow> ('x \<Rightarrow> 'y) set" where
  "actual_funcset X Y = funcset X Y \<inter> extensional X"

(* TODO function like "characteristic" surely already exists somewhere? *)
fun characteristic :: "('x \<Rightarrow> 'y) \<Rightarrow> 'y set \<Rightarrow> 'x \<Rightarrow> nat" where
  "characteristic f Y x = (if f x \<in> Y then 1 else 0)"

fun uncurry :: "('x \<Rightarrow> 'y \<Rightarrow> 'z) \<Rightarrow> ('x \<times> 'y \<Rightarrow> 'z)" where
  "uncurry f (x, y) = f x y"

lemma exists_functions_1:
  fixes
    Y :: "'y set" and X :: "'x set"
  assumes "Y \<noteq> {}"
  shows "actual_funcset X Y \<noteq> {}"
proof (safe)
  assume empty: "actual_funcset X Y = {}"
  from assms obtain y :: 'y where "y \<in> Y"
    by auto
  let ?f = "\<lambda>x. if x \<in> X then y else undefined"
  have "?f \<in> actual_funcset X Y"
    unfolding actual_funcset.simps extensional_def Pi_def
    using \<open>y \<in> Y\<close>
    by simp
  thus "False"
    using empty
    by blast
qed

lemma exists_functions_2:
  shows "actual_funcset {} {} \<noteq> {}"
proof -
  let ?f = "\<lambda>x. undefined"
  have "?f \<in> actual_funcset {} {}"
    unfolding actual_funcset.simps Pi_def extensional_def
    by simp
  thus ?thesis
    by simp
qed

lemma sum_coincide: 
  fixes
    X :: "'x set" and
    f :: "'x \<Rightarrow> real" and g :: "'x \<Rightarrow> real"
  assumes
    "finite X"
    "\<forall>x \<in> X. f x = g x"
  shows
    "(\<Sum>x\<in>X. f x) = (\<Sum>x\<in>X. g x)"
  using assms
proof (induction "card X" arbitrary: X, simp)
  fix 
    n :: nat and
    X :: "'x set"
  assume
    card: "Suc n = card X" and
    fin: "finite X" and
    coinc: "\<forall>x\<in>X. f x = g x" and
    hyp: "(\<And>X. n = card X \<Longrightarrow> finite X \<Longrightarrow> \<forall>x\<in>X. f x = g x \<Longrightarrow> sum f X = sum g X)"
  hence "X \<noteq> {}"
    by auto
  then obtain x :: 'x where "x \<in> X"
    by blast
  hence "card (X - {x}) = n"
    using card
    by simp
  hence "sum f (X - {x}) = sum g (X - {x})"
    using fin coinc hyp \<open>x \<in> X\<close>
    by simp
  moreover have "sum f (X - {x}) = sum f X - f x \<and> sum g (X - {x}) = sum g X - g x"
    using fin \<open>x \<in> X\<close>
    by (simp add: sum_diff1)
  moreover have "f x = g x"
    using \<open>x \<in> X\<close> coinc
    by blast
  ultimately show "sum f X = sum g X"
    using fin hyp[of X]
    by linarith
qed 

lemma set_card: 
  fixes 
    X :: "'x set" and
    \<phi> :: "'x \<Rightarrow> bool"
  assumes
    "finite X"
  shows
    "card {x | x. x \<in> X \<and> \<phi> x} = sum (\<lambda>x. if (\<phi> x) then 1::nat else 0) X"
proof -
  have "X = {x | x. x \<in> X \<and> \<phi> x} \<union> {x | x. x \<in> X \<and> \<not> \<phi> x}"
    by blast
  moreover have "{x | x. x \<in> X \<and> \<phi> x} \<inter> {x | x. x \<in> X \<and> \<not> \<phi> x} = {}"
    by blast
  moreover have "finite {x | x. x \<in> X \<and> \<phi> x}"
    using assms
    by simp
  moreover have "finite {x | x. x \<in> X \<and> \<not> \<phi> x}"
    using assms
    by simp
  ultimately have split_sum:
    "sum (\<lambda>x. if (\<phi> x) then 1::nat else 0) X = 
      sum (\<lambda>x. if (\<phi> x) then 1::nat else 0) {x | x. x \<in> X \<and> \<phi> x}
      + sum (\<lambda>x. if (\<phi> x) then 1::nat else 0) {x | x. x \<in> X \<and> \<not> \<phi> x}"
    using sum.union_disjoint[of "{x | x. x \<in> X \<and> \<phi> x}" "{x | x. x \<in> X \<and> \<not> \<phi> x}"]
    by (metis (no_types, lifting))
  have "\<forall>x \<in> {x | x. x \<in> X \<and> \<not> \<phi> x}. (\<lambda>x. if (\<phi> x) then 1::nat else 0) x = 0"
    by simp
  hence "sum (\<lambda>x. if (\<phi> x) then 1::nat else 0) {x | x. x \<in> X \<and> \<not> \<phi> x} = 0"
    by (rule sum.neutral)
  hence constr_sum:
    "sum (\<lambda>x. if (\<phi> x) then 1::nat else 0) X =
      sum (\<lambda>x. if (\<phi> x) then 1::nat else 0) {x | x. x \<in> X \<and> \<phi> x}"
    using split_sum
    by presburger
  have "\<forall>x \<in> {x | x. x \<in> X \<and> \<phi> x}. (\<lambda>x. if (\<phi> x) then 1::nat else 0) x = (\<lambda>x. 1) x"
    by simp
  hence 
    "sum (\<lambda>x. if (\<phi> x) then 1::nat else 0) {x | x. x \<in> X \<and> \<phi> x} = 
      sum (\<lambda>x. 1) {x | x. x \<in> X \<and> \<phi> x}"
    using sum_coincide[of "{x | x. x \<in> X \<and> \<phi> x}" "(\<lambda>x. if (\<phi> x) then 1::nat else 0)" "\<lambda>x. 1"] 
    by simp
  also have "... = card {x | x. x \<in> X \<and> \<phi> x}"
    using card_eq_sum[of "{x | x. x \<in> X \<and> \<phi> x}"]
    by simp
  finally have 
    "sum (\<lambda>x. if (\<phi> x) then 1::nat else 0) {x | x. x \<in> X \<and> \<phi> x} = card {x | x. x \<in> X \<and> \<phi> x}"
    by simp
  thus "card {x |x. x \<in> X \<and> \<phi> x} = (\<Sum>x\<in>X. if \<phi> x then 1 else 0)"
    using constr_sum
    by simp
qed

lemma card_funcset: 
  fixes
    X :: "'x set" and Y :: "'y set"
  assumes
    "finite X" and "finite Y"
  shows
    "card (actual_funcset X Y) = (card Y)^(card X)"
  using assms
proof (induction "card X" arbitrary: X)
  fix
    X :: "'x set"
  assume 
    "0 = card X"
    "finite X"
  hence "actual_funcset X Y = {(\<lambda>x. undefined)}"
    by simp
  hence "card (actual_funcset X Y) = 1"
    by simp
  moreover have "card Y ^ card X = 1"
    using assms \<open>0 = card X\<close>
    by simp
  ultimately show "card (actual_funcset X Y) = card Y ^ card X"
    by argo
next
  fix
    n :: nat and
    X :: "'x set"
  assume
    card: "Suc n = card X" and
    fin: "finite X" and
    hyp: 
      "(\<And>X. n = card (X::'x set) \<Longrightarrow> finite X \<Longrightarrow> finite Y \<Longrightarrow> 
              card (actual_funcset X Y) = card Y ^ card X)"
  hence "X \<noteq> {}"
    by auto
  then obtain x :: 'x where "x \<in> X"
    by blast
  hence card_m1: "card (X - {x}) = n"
    using card
    by simp
  hence card': "card (actual_funcset (X - {x}) Y) = card Y ^ card (X - {x})"
    using fin hyp[of "X - {x}"] assms(2) 
    by blast
  let ?F = "\<lambda>(f,y). (\<lambda>z. if z \<in> X then (if z = x then y else (f z)) else undefined)"
  have "actual_funcset X Y = ?F ` ((actual_funcset (X - {x}) Y) \<times> Y)"
  proof (safe, goal_cases)
    case (1 f)
    let ?f = "\<lambda>z. if z \<in> X - {x} then f z else undefined"
    have "f = ?F (?f, f x)"
      using 1
      unfolding actual_funcset.simps extensional_def Pi_def
      by auto
    moreover have "?f \<in> actual_funcset (X - {x}) Y"
      using 1
      unfolding actual_funcset.simps extensional_def Pi_def
      by simp
    moreover have "f x \<in> Y"
      using 1 \<open>x \<in> X\<close>
      unfolding actual_funcset.simps extensional_def Pi_def
      by blast
    ultimately show ?case
      by blast
  next
    case (2 _ f y)
    hence "\<forall>z \<in> X - {x}. ?F (f, y) z \<in> Y"
      unfolding actual_funcset.simps Pi_def
      by simp
    moreover have "?F (f, y) x \<in> Y"
      using 2 \<open>x \<in> X\<close>
      by simp
    moreover have "\<forall>z. z \<notin> X \<longrightarrow> ?F (f, y) z = undefined"
      by simp
    ultimately show ?case
      unfolding actual_funcset.simps Pi_def extensional_def
      by auto
  qed
  moreover have bij: "bij_betw ?F ((actual_funcset (X - {x}) Y) \<times> Y) (actual_funcset X Y)"
  proof (rule bij_betw_imageI, safe, goal_cases)
    case 1
    { (* Show that any two functions that have the same image under ?F are already identical *)
      fix f :: "'x \<Rightarrow> 'y" and y :: 'y and g :: "'x \<Rightarrow> 'y" and z :: 'y
      assume 
        funcset_f: "f \<in> actual_funcset (X - {x}) Y" and
        funcset_g: "g \<in> actual_funcset (X - {x}) Y" and
        eq_im: "?F (f, y) = ?F (g, z)" and 
        "y \<in> Y" and "z \<in> Y"
      hence "?F (f, y) x = ?F (g, z) x"
        by simp
      hence eq_snd: "y = z"
        using \<open>x \<in> X\<close>
        by simp
      have "\<forall>a. a \<in> X - {x} \<longrightarrow> ?F (f, y) a = f a"
        by simp
      moreover have "\<forall>a. a \<in> X - {x} \<longrightarrow> ?F (g, z) a = g a"
        by simp
      moreover have "\<forall>a. a \<in> X - {x} \<longrightarrow> ?F (f, y) a = ?F (g, z) a"
        using eq_im
        by metis
      ultimately have "\<forall>a. a \<in> X - {x} \<longrightarrow> f a = g a"
        by presburger
      moreover have "\<forall>a. a \<notin> X - {x} \<longrightarrow> f a = undefined"
        using funcset_f
        unfolding actual_funcset.simps extensional_def
        by simp
      moreover have "\<forall>a. a \<notin> X - {x} \<longrightarrow> g a = undefined"
        using funcset_g
        unfolding actual_funcset.simps extensional_def
        by simp
      ultimately have "\<forall>a. f a = g a"
        by metis
      hence "(f, y) = (g, z)"
        using eq_snd
        by presburger
    }
    thus ?case 
      unfolding inj_on_def
      by simp
  next
    case (2 _ f y)
    thus ?case 
      unfolding actual_funcset.simps extensional_def Pi_def
      by simp
  next
    case (3 f)
    let ?g = "\<lambda>z. if z \<in> X - {x} then f z else undefined"
    have "f = ?F (?g, f x)"
      using 3
      unfolding actual_funcset.simps extensional_def 
      by auto
    moreover have "?g \<in> actual_funcset (X - {x}) Y"
      using 3
      unfolding actual_funcset.simps extensional_def Pi_def
      by simp
    moreover have "f x \<in> Y"
      using 3 \<open>x \<in> X\<close>
      unfolding actual_funcset.simps Pi_def
      by simp
    ultimately show ?case
      by blast
  qed 
  ultimately have "card ((actual_funcset (X - {x}) Y) \<times> Y) = card (actual_funcset X Y)"
    using bij_betw_same_card[OF bij]
    by satx
  moreover have 
    "card ((actual_funcset (X - {x}) Y) \<times> Y) = card Y * card (actual_funcset (X - {x}) Y)"
    using assms card_cartesian_product[of "actual_funcset (X - {x}) Y" Y]
    by algebra
  moreover have "card Y * card Y ^ card (X - {x}) = card Y ^ card X"
    using \<open>x \<in> X\<close> assms card card_m1 power_Suc2[of "card Y" "card (X - {x})"]
    by simp
  ultimately show "card (actual_funcset X Y) = card Y ^ card X"
    using card'
    by simp
qed


lemma fin_funcset:
    fixes
    X :: "'x set" and Y :: "'y set"
  assumes
    "finite X" and "finite Y"
  shows
    "finite (actual_funcset X Y)"
proof (cases "Y = {}")
  case True
  hence "X = {} \<Longrightarrow> actual_funcset X Y = {\<lambda>x. undefined}"
    by simp
  moreover have "X \<noteq> {} \<Longrightarrow> actual_funcset X Y = {}"
    using True
    by auto
  ultimately show ?thesis
    by fastforce
next
  case False
  hence "card Y > 0"
    using assms
    by auto
  hence "card (actual_funcset X Y) > 0"
    using card_funcset[of X Y, OF assms]
    by presburger
  then show ?thesis 
    by (rule card_ge_0_finite)
qed

section \<open>Simple Voting Games\<close>

text \<open>
A simple voting game is a tuple consisting of a set (of voters) 
and a set family (of voter coalitions).
\<close>
type_synonym 'v Simple_Voting_Game = "'v set \<times> ('v set set)"

abbreviation voters_svg :: "'v Simple_Voting_Game \<Rightarrow> 'v set" where
  "voters_svg G \<equiv> fst G"

abbreviation coalitions :: "'v Simple_Voting_Game \<Rightarrow> 'v set set" where
  "coalitions G \<equiv> snd G"

fun aggregation_method :: 
  "'b \<Rightarrow> 'b \<Rightarrow> 'r \<Rightarrow> 'r \<Rightarrow> 'v Simple_Voting_Game \<Rightarrow> (('v \<Rightarrow> 'b) \<Rightarrow> 'r)" where
  "aggregation_method ball1 ball2 res1 res2 (V, \<F>) p = 
    (if (preimg_in V p {ball1} \<in> \<F>) then res1 else res2)" (* TODO require p to be valid *)

fun monotone_SVG :: "'v Simple_Voting_Game \<Rightarrow> bool" where
  "monotone_SVG (V, \<F>) = (\<forall>S \<in> Pow V. \<forall>T \<in> Pow V. S \<subseteq> T \<longrightarrow> S \<in> \<F> \<longrightarrow> T \<in> \<F>)"

definition monotone_SVGs :: "'v Simple_Voting_Game set" where
  "monotone_SVGs \<equiv> Collect monotone_SVG"

subsection \<open>Voting Power Indices on Simple Voting Games\<close>

fun swing_vote_svg :: "'v set set \<Rightarrow> 'v \<Rightarrow> 'v set \<Rightarrow> ereal" where
  "swing_vote_svg \<F> v S = (if ((S \<union> {v}) \<in> \<F>) \<noteq> ((S - {v}) \<in> \<F>) then 1 else 0)"

text \<open>
  First formulation of a Banzhaf index for simple voting games:
  Count the number of coalitions a voter can change by switching their vote and average over those.
\<close>
fun banzhaf_svg_1 :: "('v Simple_Voting_Game, 'v) Voting_Power" where
  "banzhaf_svg_1 (V, \<F>) v = (if v \<notin> V \<or> infinite V then 0 else
    (1/(2^(card V))) * (\<Sum> S \<in> Pow V. swing_vote_svg \<F> v S))"
(* TODO: Original definition just assumes finite voter sets.
Formalizing the indices here forces one to explicitly think about infinite sets 
since every statement about the index includes infinite sets in its domain. 
Here, we define each voter's power to be 0 if V is infinite. *)

(* fun finite_test:: "nat set \<Rightarrow> bool" where
  "finite_test N = finite N"

value "finite {1::nat}" (* Zulip? *)
value "banzhaf_svg_1 ({1::nat, 2}, {{1}, {1,2}}) 1" *)

subsection \<open>Voting Power Properties on Simple Voting Games\<close>

fun banzhaf_prob_svg :: "'v Simple_Voting_Game \<Rightarrow> 'v set measure" where
  "banzhaf_prob_svg G = uniform_count_measure (Pow (fst G))"

fun is_null_player :: "'v Simple_Voting_Game \<Rightarrow> 'v \<Rightarrow> bool" where
  "is_null_player (V, \<F>) v = (range (swing_vote_svg \<F> v) = {0})"

text \<open>
  A player is called null player if they do not have any swing votes.
  A voting power index satisfies the null player axiom if null players have 0 power in every SVG.
\<close>
fun null_player_axiom_svg_on :: "('v Simple_Voting_Game, 'v) Voting_Power_Axiom" where
  "null_player_axiom_svg_on \<G> \<delta> = 
    (\<forall>G \<in> \<G>. \<forall>v \<in> voters_svg G. is_null_player G v \<longrightarrow> \<delta> G v = 0)"

fun block_svg :: "'v Simple_Voting_Game \<Rightarrow> 'v Simple_Voting_Game \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> bool" where
  "block_svg G G' v w x = (
    x \<notin> voters_svg G \<and>
    voters_svg G' = voters_svg G - {v, w} \<union> {x} \<and> 
    coalitions G' = {S - {v, w} \<union> {x} |S. v \<in> S \<and> w \<in> S \<and> S \<in> coalitions G} \<union>
                    {S |S. v \<notin> S \<and> w \<notin> S \<and> S \<in> coalitions G}
  )"

(* TODO: Formulate axiom over all SVGs that have some merged voter instead of calculating block SVG *)
fun block_axiom_svg_on ::
  "('v Simple_Voting_Game, 'v) Voting_Power_Axiom" where
  "block_axiom_svg_on \<G> \<delta> = (\<forall>G \<in> \<G>. \<forall>v \<in> voters_svg G. \<forall>w \<in> voters_svg G. \<forall>x.
    (w \<noteq> v \<longrightarrow> (\<forall>G'. block_svg G G' v w x \<longrightarrow> (\<delta> G' x \<ge> Max{\<delta> G v, \<delta> G w}))))"

fun voter_isomorphism_SVG :: "('v \<Rightarrow> 'v) \<Rightarrow> 'v Simple_Voting_Game \<Rightarrow> 'v Simple_Voting_Game" where
  "voter_isomorphism_SVG \<pi> (V, \<F>) = (\<pi> ` V, (image \<pi>) ` \<F>)"

fun iso_svg :: 
  "('v \<Rightarrow> 'v) \<Rightarrow> 'v Simple_Voting_Game \<Rightarrow> 'v Simple_Voting_Game \<Rightarrow> bool" where
  "iso_svg \<phi> G1 G2 = 
    (bij_betw \<phi> (voters_svg G1) (voters_svg G2) \<and> G2 = voter_isomorphism_SVG \<phi> G1)"

fun symmetry_axiom_svg_on :: "('v Simple_Voting_Game, 'v) Voting_Power_Axiom" where
  "symmetry_axiom_svg_on \<G> \<delta> = 
    (\<forall>G1 \<in> \<G>. \<forall>G2 \<in> \<G>. \<forall>\<phi>. iso_svg \<phi> G1 G2 \<longrightarrow> (\<forall>v \<in> voters_svg G1. \<delta> G1 v = \<delta> G2 (\<phi> v)))"

fun meet_svg :: "'v Simple_Voting_Game \<Rightarrow> 'v Simple_Voting_Game \<Rightarrow> 'v Simple_Voting_Game" where
  "meet_svg G1 G2 = (voters_svg G1, coalitions G1 \<union> coalitions G2)"

fun join_svg :: "'v Simple_Voting_Game \<Rightarrow> 'v Simple_Voting_Game \<Rightarrow> 'v Simple_Voting_Game" where
  "join_svg G1 G2 = (voters_svg G1, coalitions G1 \<inter> coalitions G2)"

subsection \<open>Property Proofs on Simple Voting Games\<close>

lemma banzhaf_1_satisfies_null_player_axiom_svg: 
  "null_player_axiom_svg_on UNIV banzhaf_svg_1"
proof (unfold null_player_axiom_svg_on.simps fst_def, safe)
  fix
    V :: "'a set" and
    \<F> :: "'a set set" and
    v :: 'a
  assume
    "v \<in> V" and "is_null_player (V, \<F>) v"
  hence "range (swing_vote_svg \<F> v) = {0}"
  by simp
  hence "\<forall>S. swing_vote_svg \<F> v S = 0"
    unfolding fst_def snd_def
    by fast
  hence "(\<Sum> S \<in> Pow V. swing_vote_svg \<F> v S) = 0"
    by simp
  thus "banzhaf_svg_1 (V, \<F>) v = 0"
    by simp
qed 

lemma banzhaf_1_satisfies_symmetry_axiom:
  "symmetry_axiom_svg_on UNIV banzhaf_svg_1"
  sorry

lemma banzhaf_1_satisfies_block_axiom: 
  "block_axiom_svg_on monotone_SVGs banzhaf_svg_1"
proof (simp only: block_axiom_svg_on.simps fst_def snd_def, safe, goal_cases)
  case (1 V \<F> v w x V' \<F>')
  hence merged_vot_set: "V' = V - {w, v} \<union> {x}"
    by auto
  from 1 show ?case
  proof (cases "finite V")
    case True
    let ?\<F> = "{S - {w} |S. (v \<in> S \<longleftrightarrow> w \<in> S) \<and> S \<in> \<F>}"
    let ?n = "card V"
    have "card V = Suc (card (V - {w}))"
      using 1 True card_Suc_Diff1
      by metis
    hence "1/(2^(card V)) = 1/(2 * 2^(card (V - {w})))" 
      by simp
    hence "2 * (1/(2^(card V))) = 2 * (1/(2 * 2^(card (V - {w}))))"
      by metis
    also have "... = 1/((2::ereal)^(card (V - {w})))"
      using True \<open>w \<in> V\<close>
      by (simp add: one_ereal_def) (* TODO why is this needed? *)
    finally have card1: "1/((2::ereal)^(card (V - {w}))) = (2::ereal) * (1/(2^(card V)))"
      by simp
    thus ?thesis (* TODO *)
      sorry
  next
    case False
    hence "infinite (V - {w, v})"
      by simp
    hence "infinite V'"
      using merged_vot_set
      by simp
    hence "banzhaf_svg_1 (V', \<F>') x = 0"
      by simp
    moreover have "Max {banzhaf_svg_1 (V, \<F>) v, banzhaf_svg_1 (V, \<F>) w} = 0"
      using False
      by simp
    ultimately show ?thesis  
      by order
  qed
qed

lemma banzhaf_1_is_prob_svg:
  fixes
    V :: "'v set" and
    \<F> :: "'v set set" and
    v :: 'v
  assumes
    "finite V" and "\<F> \<subseteq> Pow V" and "v \<in> V"
  shows
    "banzhaf_svg_1 (V, \<F>) v = emeasure (banzhaf_prob_svg (V, \<F>)) {S | S. swing_vote_svg \<F> v S = 1}"
proof -
  let ?swings = "{S | S. swing_vote_svg \<F> v S = 1}"
  have "\<forall>S. swing_vote_svg \<F> v S = 1 \<longrightarrow> S \<subseteq> V"
  proof (simp, safe)
    fix 
      S :: "'v set" and
      x :: 'v
    assume 
      "insert v S \<in> \<F>" and "x \<in> S"
    hence "S \<union> {v} \<subseteq> V"
      using assms(2)
      by blast
    thus "x \<in> V"
      using \<open>x \<in> S\<close>
      by blast
  next
    fix 
      S :: "'v set" and
      x :: 'v
    assume 
      "x \<in> S" and "x \<notin> V" and "S - {v} \<in> \<F>"
    hence "S - {v} \<subseteq> V"
      using assms(2)
      by blast
    hence "S \<subseteq> V"
      using assms(2) assms(3)
      by blast
    hence "x \<in> V"
      using \<open>x \<in> S\<close>
      by blast
    thus "False"
      using \<open>x \<notin> V\<close>
      by blast
  qed
  hence subset: "?swings \<subseteq> Pow V"
    by blast
  moreover have fin_pow: "finite (Pow V)"
    using assms(1)
    by simp
  ultimately have rewrite_prob:
    "emeasure (banzhaf_prob_svg (V, \<F>)) {S | S. swing_vote_svg \<F> v S = 1}
      = (card {S | S. swing_vote_svg \<F> v S = 1})/(card (Pow V))"
    unfolding banzhaf_prob_svg.simps
    using emeasure_uniform_count_measure[of "Pow V" ?swings]
    by simp
  have "ereal (1/(2^(card V))) = ereal (1/(card (Pow V)))"
    using assms(1) Power.card_Pow[of V, OF assms(1)]
    by simp
  hence 
    "\<forall>x::ereal. (1/(2^(card V))) * x = (1/(card (Pow V))) * x"
    by (metis ereal_divide ereal_power numeral_eq_ereal one_ereal_def power_eq_0_iff zero_neq_numeral)
  hence rewrite_pow':
    "(1/(2^(card V))) * (\<Sum> S \<in> Pow V. swing_vote_svg \<F> v S)
    = (1/(card (Pow V))) * (\<Sum> S \<in> Pow V. swing_vote_svg \<F> v S)"
    by simp

  have swing_vote: 
    "(\<lambda>S. (if swing_vote_svg \<F> v S = 1 then 1 else 0)) = (\<lambda>S. swing_vote_svg \<F> v S)"
    by auto
  have swings: "?swings = {S |S. S \<in> Pow V \<and> swing_vote_svg \<F> v S = 1}"
    using subset
    by blast

  hence "card ?swings = card {S |S. S \<in> Pow V \<and> swing_vote_svg \<F> v S = 1}"
    by simp
  also have 
    "... = (\<Sum>S\<in>Pow V. if swing_vote_svg \<F> v S = 1 then 1 else 0)"
    by (rule set_card[of "Pow V" "\<lambda>S. swing_vote_svg \<F> v S = 1", OF fin_pow])
  also have 
    "... = (\<Sum>S\<in>Pow V. swing_vote_svg \<F> v S)"
    using swing_vote
    sorry
  finally have
    "(\<Sum>S\<in>Pow V. swing_vote_svg \<F> v S) = card {S |S. swing_vote_svg \<F> v S = 1}"
    by simp
  hence rewrite_pow:
    "banzhaf_svg_1 (V, \<F>) v = (1/(card (Pow V))) * card {S | S. swing_vote_svg \<F> v S = 1}"
    using rewrite_pow'
    sorry
  thus ?thesis
    using rewrite_prob
    by simp
qed

section \<open>Voting Rules\<close>

fun differ_only_on :: "'v \<Rightarrow> ('v \<Rightarrow> 'b) \<Rightarrow> ('v \<Rightarrow> 'b) \<Rightarrow> bool" where
  "differ_only_on v p p' = (\<forall>x. p x \<noteq> p' x \<longrightarrow> x = v)"

lemma neq_differ_exactly_on:
  fixes f :: "'x \<Rightarrow> 'y" and g :: "'x \<Rightarrow> 'y" and x :: 'x and x' :: 'x
  assumes "f \<noteq> g" and "differ_only_on x f g"
  shows "(f x' \<noteq> g x') = (x' = x)"
proof -
  have "\<exists>x''. f x'' \<noteq> g x''"
    using assms
    by auto
  then obtain x'' :: 'x where "f x'' \<noteq> g x''"
    by meson
  moreover have "x'' \<noteq> x \<Longrightarrow> f x'' = g x''"
    using assms
    by auto
  ultimately have "f x \<noteq> g x"
    by metis
  hence "x' = x \<Longrightarrow> f x' \<noteq> g x'"
    by simp
  moreover have "f x' \<noteq> g x' \<Longrightarrow> x' = x"
    using assms
    by simp
  ultimately show ?thesis
    by satx
qed

subsection \<open>Voting Power Indices on Voting Rules\<close>

fun swing_vote_rule :: "(('v \<Rightarrow> 'b) \<Rightarrow> 'r) \<Rightarrow> 'v \<Rightarrow> ('v \<Rightarrow> 'b) \<Rightarrow> ('v \<Rightarrow> 'b) \<Rightarrow> ereal" where
  "swing_vote_rule f v p p' = (if (differ_only_on v p p' \<and> f p \<noteq> f p') then 1 else 0)"

text \<open>
  First formulation of a Banzhaf index for voting rules:
  Count the number of profiles where the outcome would change if a voter changed their ballot
  while all other voters kept theirs, then average over all profiles.
\<close>
fun banzhaf_rule_1 :: "(('v, 'b, 'r) Voting_Rule, 'v) Voting_Power" where
  "banzhaf_rule_1 (V, B, R, f) v = (if infinite V then 0 else
    (1/(real ((card B)^(card V)))) * 
      (\<Sum> p \<in> actual_funcset V B. 
        Max {characteristic (swing_vote_rule f v p) {1} q | q. q \<in> actual_funcset V B}))" 

(* TODO: test value banzhaf_rule_1 *)

(* Banzhaf index where probability interpretation breaks: *)
fun banzhaf_rule_2 :: "('v, 'b, 'r) Voting_Rule \<Rightarrow> 'v \<Rightarrow> ereal" where
  "banzhaf_rule_2 (V, B, R, f) v = 
    (1/(real ((card B)^(card V)))) * 
      (\<Sum> p \<in> actual_funcset V B. \<Sum> q \<in> actual_funcset V B. (swing_vote_rule f v p q))" 
(* Additional danger of not stating the intended voting power measure
when formalizing with weird types: Almost wrote \<^latex>\<open>p \<in> UNIV\<close> here *)

subsection \<open>Voting Power Properties on Voting Rules\<close>

fun is_null_player_rule :: "('v, 'b, 'r) Voting_Rule \<Rightarrow> 'v \<Rightarrow> bool" where
  "is_null_player_rule f v = (\<forall>p. range (swing_vote_rule (rule f) v p) = {0})"

fun null_player_axiom_rule :: "(('v, 'b, 'r) Voting_Rule, 'v) Voting_Power_Axiom" where
  "null_player_axiom_rule \<R> \<delta> = (\<forall>f \<in> \<R>. \<forall>v \<in> voters f. is_null_player_rule f v \<longrightarrow> \<delta> f v = 0)"

fun block_profile :: "'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> ('v \<Rightarrow> 'b) \<Rightarrow> ('v \<Rightarrow> 'b)" where
  "block_profile v w x p y = (if y \<in> {v,w} then p x else p y)"

fun block_tally :: "'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> (('v \<Rightarrow> 'b) \<Rightarrow> 'r) \<Rightarrow> (('v \<Rightarrow> 'b) \<Rightarrow> 'r)" where
  "block_tally v w x f p = f (block_profile v w x p)"

fun block_rule :: 
  "('v, 'b, 'r) Voting_Rule \<Rightarrow> ('v, 'b, 'r) Voting_Rule \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> bool" where
  "block_rule (V,B,R,f) (V',B',R',f') v w x = 
    (x \<notin> V \<and> V' = V - {v,w} \<union> {x} \<and> B' = B \<and> R' = R \<and> f' = block_tally v w x f)"

fun block_axiom_rule :: "(('v, 'b, 'r) Voting_Rule, 'v) Voting_Power_Axiom" where
  "block_axiom_rule \<R> \<delta> = 
    (\<forall>f \<in> \<R>. \<forall>f'. \<forall>v \<in> (voters f). \<forall>w \<in> (voters f). \<forall>x.
      block_rule f f' v w x \<longrightarrow> \<delta> f' x \<ge> Max{\<delta> f v, \<delta> f w})"

fun banzhaf_prob_rule :: "('v, 'b, 'r) Voting_Rule \<Rightarrow> ('v \<Rightarrow> 'b) measure" where
  "banzhaf_prob_rule (V, B, R, f) = uniform_count_measure (actual_funcset V B)"

fun symmetry_axiom_rule :: "(('v, 'b, 'r) Voting_Rule, 'v) Voting_Power_Axiom" where
  "symmetry_axiom_rule \<R> \<delta> =
    (True)" (* TODO *)

subsection \<open>Property Proofs on Voting Rules\<close>

lemma banzhaf_1_satisfies_null_player_axiom:
  "null_player_axiom_rule UNIV banzhaf_rule_1"
proof (simp only: null_player_axiom_rule.simps, safe, goal_cases)
  case (1 V B R f v)
  show ?case
  proof (cases "B = {} \<and> V \<noteq> {}")
    case True
    hence "actual_funcset V B = {}"
      unfolding actual_funcset.simps Pi_def extensional_def
      by simp
    hence "(\<Sum> p \<in> actual_funcset V B. 
          Max {characteristic (swing_vote_rule f v p) {1} q | q. q \<in> actual_funcset V B}) = 0"
      by simp
    thus ?thesis
      by simp
  next
    case False
    hence cases: "B \<noteq> {} \<or> (B = {} \<and> V = {})"
      by blast
    have "\<forall>p. range (swing_vote_rule f v p) = {0}"
      using 1
      by simp
    hence "\<forall>p q. swing_vote_rule f v p q = 0"
      by blast
    hence "\<forall>p q. characteristic (swing_vote_rule f v p) {1} q = 0"
      by simp
    moreover have "actual_funcset V B \<noteq> {}"
      using cases
      by (metis exists_functions_1 exists_functions_2)
    ultimately have
      "\<forall>p. {characteristic (swing_vote_rule f v p) {1} q | q. q \<in> actual_funcset V B} = {0}"
      by auto
    hence "(\<Sum> p \<in> actual_funcset V B. 
          Max {characteristic (swing_vote_rule f v p) {1} q | q. q \<in> actual_funcset V B}) = 0"
      by simp
    thus ?thesis
      by simp
  qed
qed
                                                
lemma banzhaf_1_is_prob_rule:
  fixes
    X :: "('v, 'b, 'r) Voting_Rule" and
    v :: 'v
  assumes
    "finite (voters X)" and "finite (ballots X)" and "v \<in> V"
  shows
    "banzhaf_rule_1 X v = emeasure (banzhaf_prob_rule X) 
      {p | p. p \<in> actual_funcset (voters X) (ballots X) 
        \<and> (\<exists>q \<in> actual_funcset (voters X) (ballots X). swing_vote_rule (rule X) v p q = 1)}"
proof -
  let ?V = "voters X"
  let ?B = "ballots X"
  let ?f = "rule X"
  let ?swings = 
    "{p |p. p \<in> actual_funcset ?V ?B \<and> (\<exists>q\<in>actual_funcset ?V ?B. swing_vote_rule ?f v p q = 1)}"
  have "finite (actual_funcset ?V ?B)"
    sorry
  moreover have "?swings \<subseteq> actual_funcset ?V ?B"
    sorry
  ultimately have prob:
    "emeasure (uniform_count_measure (actual_funcset ?V ?B)) ?swings
      = (real (card ?swings))/(real (card (actual_funcset ?V ?B)))"
    using emeasure_uniform_count_measure[of "actual_funcset ?V ?B" ?swings]
    by simp
  have "X = (?V, ?B, results X, ?f)"
    by simp
  hence
    "banzhaf_prob_rule X = uniform_count_measure (actual_funcset ?V ?B)"
    by (metis banzhaf_prob_rule.simps)
  with prob have prob_rewrite:
    "banzhaf_prob_rule X ?swings = (real (card ?swings))/(real (card (actual_funcset ?V ?B)))"
    by simp
  have
    "(\<Sum> p \<in> actual_funcset ?V ?B. 
        Max {characteristic (swing_vote_rule ?f v p) {1} q | q. q \<in> actual_funcset ?V ?B})
      = card ?swings"
    sorry
  hence
    "banzhaf_rule_1 X v = (1/(real ((card ?B)^(card ?V)))) * (card ?swings)"
    sorry
  hence
    "banzhaf_rule_1 X v = (1/(real (card (actual_funcset ?V ?B)))) * (card ?swings)"
    using card_funcset[of ?V ?B] assms
    sorry
  hence power_rewrite:
    "banzhaf_rule_1 X v = (real (card ?swings))/(real (card (actual_funcset ?V ?B)))"
    by argo
  thus ?thesis
    using prob_rewrite
    by simp
qed

text \<open>
  The second Banzhaf definition on voting rules generally is an expected value rather 
  than a probability distribution. 
  However, depending on the voter and the event, it may align with individual probabilities.
  
  To make the difference between this probabilistic interpretation and the one from
  banzhaf_1_is_prob_rule clear, we show that if there is a voter who is able to influence the
  election result in at least one way for every ballot profile and at least two ways for at
  least one ballot profile, their Banzhaf index is > 1 and thus no probability.
\<close>
lemma baby_example_banzhaf_2_not_prob:
  fixes                                    
    X :: "('v, 'b, 'r) Voting_Rule" and
    v :: 'v              
  assumes
    "finite (voters X)" and 
    "finite (ballots X)" and 
    "v \<in> V" and
    always_influence: (* v can influence the election result in every profile *)
      "\<forall>p \<in> actual_funcset (voters X) (ballots X). \<exists>q \<in> actual_funcset (voters X) (ballots X). 
        swing_vote_rule (rule X) v p q = 1" and
    influence_options: (* v has multiple options to influence the election result in at least one profile *)
      "\<exists>p \<in> actual_funcset (voters X) (ballots X). 
        \<exists>q \<in> actual_funcset (voters X) (ballots X). \<exists>q' \<in> actual_funcset (voters X) (ballots X). 
          q \<noteq> q' \<and> swing_vote_rule (rule X) v p q = 1 \<and> swing_vote_rule (rule X) v p q' = 1"
  shows
    "banzhaf_rule_2 X v > 1"
  sorry

lemma banzhaf_2_is_expectation_rule:
  "True" (* is it? *)
  sorry

section \<open>Strategic Games\<close>

subsection \<open>Voting Power Indices on Strategic Games\<close>

text \<open>
  First formulation of a Banzhaf index for strategic games: 
  The same as the Banzhaf index of the induced voting rule.
\<close>
fun banzhaf_strat_1 :: "('v, 'a, 'r) Strategic_Game \<Rightarrow> 'v \<Rightarrow> ereal" where
  "banzhaf_strat_1 G v = banzhaf_rule_1 (strat_rule G) v" (* TODO *)

text \<open>
  Second formulation of a Banzhaf index for strategic games: 
  Assumes the optimal strategy profiles from a given solution concept are uniformly distributed.
\<close>
fun banzhaf_strat_2 :: 
  "('v, 'a, 'r) Strategic_Game \<Rightarrow> ('v, 'a, 'r) Solution_Concept \<Rightarrow> 'v \<Rightarrow> ereal" where
  "banzhaf_strat_2 G C v = (1/(card (C G))) 
    * (\<Sum> A \<in> C G. (Max {characteristic (swing_vote_rule (outcome_map G) v A) {1} A' | A'. A' \<in> C G}))"

text \<open>
  Third formulation of a Banzhaf index for strategic games: 
  Includes the notion of success. 
  A voter v's successful swing vote is a strategy profile A where v prefers the result after 
  changing their vote to the result in A. 
\<close>
(* TODO type abbreviations for frequent types *)
fun swing_vote_success ::
  "('v, 'a, 'r) Strategic_Game \<Rightarrow> 'v \<Rightarrow> ('v \<Rightarrow> 'a) \<Rightarrow> ('v \<Rightarrow> 'a) \<Rightarrow> ereal" where
  "swing_vote_success G v A A' = 
    (if (differ_only_on v A A' 
      \<and> (outcome_map G A, outcome_map G A') \<in> preferences G v) then 1 else 0)"

fun banzhaf_strat_3 ::
  "('v, 'a, 'r) Solution_Concept \<Rightarrow> (('v, 'a, 'r) Strategic_Game, 'v) Voting_Power" where
  "banzhaf_strat_3 C G v = (1/(card (C G)))
    * (\<Sum> A \<in> C G. (Max {characteristic (swing_vote_success G v A) {1} A' | A'. A' \<in> C G}))"

subsection \<open>Voting Power Properties on Strategic Games\<close>

fun is_null_player_strat :: "('v, 'a, 'r) Strategic_Game \<Rightarrow> 'v \<Rightarrow> bool" where
  "is_null_player_strat G v = (\<forall>A. range (swing_vote_success G v A) = {0})"

fun null_player_axiom_strat :: 
  "('v, 'a, 'r) Strategic_Game set \<Rightarrow> (('v, 'a, 'r) Strategic_Game, 'v) Voting_Power \<Rightarrow> bool" where
  "null_player_axiom_strat X \<delta> = 
    (\<forall>G \<in> X. \<forall>v \<in> voters_strat G. is_null_player_strat G v \<longrightarrow> \<delta> G v = 0)"

subsection \<open>Property Proofs on Strategic Games\<close>

lemma  banzhaf_3_satisfies_null_player_axiom:
  fixes
    C :: "('v, 'a, 'r) Solution_Concept"
  shows
    "null_player_axiom_strat UNIV (banzhaf_strat_3 C)"
  sorry

section \<open>Voting Power Comparison\<close>

section \<open>Ad Hoc Definitions\<close>

(*
text \<open>
Ad hoc definition: A voting power index formulated on the domain of voting rules is equivalent
to a voting power index on the domain of SVGs if they yield the same power given equivalent inputs.
\<close>
definition svg_rule_power_equivalence ::
  "(('v, 'b, 'r) Voting_Rule, 'v) Voting_Power \<Rightarrow> ('v Simple_Voting_Game, 'v) Voting_Power \<Rightarrow> bool"
  where 
    "svg_rule_power_equivalence \<delta>1 \<delta>2 = (
      \<forall>\<R> \<G> ball1 ball2 res1 res2. svg_rule_equivalence ball1 ball2 res1 res2 \<R> \<G> \<longrightarrow> 
        (\<forall>v \<in> voters \<R> \<inter> fst \<G>. \<delta>1 \<R> v = \<delta>2 \<G> v)
    )"

text \<open>
Ad hoc definition: Two voting power axioms, where one is formulated on the domain of SVG voting
power indices and the other is defined on the domain of voting rule power indices, are equivalent
if they yield the same truth values on equivalent inputs.
\<close>
definition svg_rule_axiom_equivalence ::
  "(('v, 'b, 'r) Voting_Rule, 'v) Voting_Power_Axiom \<Rightarrow> 
    ('v Simple_Voting_Game, 'v) Voting_Power_Axiom \<Rightarrow> bool" where
  "svg_rule_axiom_equivalence \<phi>1 \<phi>2 = (\<forall>m1 m2 \<delta>1 \<delta>2 ball1 ball2 res1 res2. 
    svg_rule_equivalence ball1 ball2 res1 res2 m1 m2 \<and> svg_rule_power_equivalence \<delta>1 \<delta>2 \<longrightarrow> 
    (\<phi>1 {m1} \<delta>1 \<longleftrightarrow> \<phi>2 {m2} \<delta>2))"

section \<open>Auxiliary Lemmas\<close>

text \<open>
The preimage of a single element y under a bijective map is the 
singleton set containing exactly the inverse of y under the bijection.
\<close>
lemma preimg_the_inv:
  fixes
    X :: "'x set" and Y :: "'y set" and \<pi> :: "'x \<Rightarrow> 'y" and y :: 'y
  assumes
    "y \<in> Y" and
    "bij_betw \<pi> X Y"
  shows "preimg_in X \<pi> {y} = {the_inv_into X \<pi> y}"
proof (safe)
  fix x :: 'x
  assume preimg: "x \<in> preimg_in X \<pi> {y}"
  hence "\<pi> x = y"
    by simp
  moreover have "x \<in> X"
    using preimg
    by simp
  ultimately show "x = the_inv_into X \<pi> y"
    using assms the_inv_into_f_f[of \<pi> X x]
    unfolding bij_betw_def
    by metis
next
  have "\<pi> (the_inv_into X \<pi> y) = y"
    using assms f_the_inv_into_f_bij_betw
    by metis
  moreover have "the_inv_into X \<pi> y \<in> X"
    using assms
    by (metis bij_betw_def image_eqI the_inv_into_onto)
  ultimately show "the_inv_into X \<pi> y \<in> preimg_in X \<pi> {y}"
    by simp
qed

text \<open>
For a given non-empty proper subset S of a given codomain and for every subset T of a given domain,
we can find a function f s.t. the preimage of S under f is precisely T.
\<close>
lemma preimg_funcset:
  fixes
    X :: "'x set" and Y :: "'y set" and S :: "'y set"
  assumes
    "S \<subseteq> Y" and "S \<noteq> Y" and "S \<noteq> {}"
  shows "{preimg_in X f S |f. f \<in> actual_funcset X Y} = Pow X"
proof (simp, safe)
  fix T :: "'x set"
  assume "T \<subseteq> X"
  obtain y :: 'y where "y \<in> Y - S"
    using assms
    by auto
  obtain s :: 'y where "s \<in> S"
    using assms
    by auto
  let ?f = "\<lambda>x. if x \<notin> X then undefined else (if x \<in> T then s else y)"
  have "?f \<in> X \<rightarrow> Y"
    unfolding Pi_def
    using \<open>y \<in> Y - S\<close> \<open>s \<in> S\<close> assms
    by auto
  moreover have "?f \<in> extensional X"
    unfolding extensional_def
    by simp
  moreover have "T = {x \<in> X. ?f x \<in> S}"
    using \<open>y \<in> Y - S\<close> \<open>s \<in> S\<close> \<open>T \<subseteq> X\<close>
    by auto
  ultimately show "\<exists>f. T = {x \<in> X. f x \<in> S} \<and> f \<in> X \<rightarrow> Y \<and> f \<in> extensional X"
    by auto
qed

text \<open>
The preimage of a non-empty set that is not the whole codomain under a 
bijective map is also non-empty and does not equal the whole domain.
\<close>
lemma preimg_bij_non_trivial: 
  fixes
    X :: "'x set" and Y :: "'y set" and S :: "'y set" and \<pi> :: "'x \<Rightarrow> 'y"
  assumes
    "bij_betw \<pi> X Y" and "S \<subseteq> Y" and "S \<noteq> {}" and "S \<noteq> Y"
  shows
    "preimg_in X \<pi> S \<noteq> {}" and "preimg_in X \<pi> S \<noteq> X"
proof (simp, safe)  
  obtain y :: 'y where "y \<in> S"
    using assms
    by auto
  hence "the_inv_into X \<pi> y \<in> X \<and> \<pi> (the_inv_into X \<pi> y) \<in> S"
    using assms bij_betwE bij_betw_the_inv_into subset_iff
    by (metis bij_betw_the_inv_into bij_betwE subset_iff f_the_inv_into_f_bij_betw)
  thus "\<exists>x. x \<in> X \<and> \<pi> x \<in> S"
    by meson
next
  assume img_S: "preimg_in X \<pi> S = X"
  from assms obtain y :: 'y where "y \<in> Y" and "y \<notin> S"
    by auto
  hence "\<pi> (the_inv_into X \<pi> y) \<notin> S"
    using assms
    by (simp add: f_the_inv_into_f_bij_betw)
  hence "the_inv_into X \<pi> y \<notin> preimg_in X \<pi> S"
    by simp
  moreover have "the_inv_into X \<pi> y \<in> X"
    using assms \<open>y \<in> Y\<close> bij_betw_the_inv_into bij_betwE
    by meson
  ultimately show "False"
    using img_S
    by metis
qed

text \<open>
A function whose codomain contains more than 1 element can be update in a single element of 
its domain by just assigning another value from the codomain to that specific element.
\<close>
(* TODO formulate using "obtains" *)
lemma update_function:
  fixes f :: "'x \<Rightarrow> 'y" and X :: "'x set" and Y :: "'y set" and x :: 'x
  assumes "x \<in> X" and "Y \<noteq> {}" and "card Y \<noteq> 1" and "f \<in> actual_funcset X Y" 
  shows
    "\<exists>g. g \<in> actual_funcset X Y \<and> f \<noteq> g \<and> differ_only_on x f g"
proof -
  have "f x \<in> Y"
    using assms
    by auto
  then obtain y :: 'y where "y \<in> Y" and "y \<noteq> f x"
    using assms is_singleton_altdef is_singletonI'
    by metis
  let ?g = "\<lambda>z. if z = x then y else f z"
  have "?g \<in> actual_funcset X Y"
    using assms \<open>y \<in> Y\<close>
    unfolding actual_funcset.simps Pi_def extensional_def
    by simp
  moreover have "differ_only_on x f ?g"
    by simp
  moreover have "f \<noteq> ?g" 
    using \<open>y \<noteq> f x\<close>
    by metis
  ultimately show ?thesis
    by meson
qed

text \<open>
If a function yields only extended reals that are not infinite, then
summing over the extended reals and casting the sum to a real yields the same value
as casting the summands to reals and then summing over the cast summands.
\<close>
(* TODO formulate without f *)
lemma ereal_sum:
  fixes X :: "'x set" and f :: "'x \<Rightarrow> ereal"
  assumes
    "\<forall>x \<in> X. f x \<notin> {\<infinity>, -\<infinity>}" and "finite X"
  shows "(\<Sum>x \<in> X. f x) = (\<Sum>x \<in> X. real_of_ereal (f x))"
(* TODO use/generalize sum_comp_morphism[of real_of_ereal f X] for carrier sets somehow? *)
  using assms
proof (induction "card X" arbitrary: X)
  case 0
  then show ?case by simp
next
  case (Suc n)
  hence "X \<noteq> {}"
    by auto
  then obtain x :: 'x where "x \<in> X" and card: "card (X - {x}) = n"
    using Suc
    by fastforce
  hence "f x \<notin> {\<infinity>, -\<infinity>}"
    using Suc
    by metis
  hence eq: "ereal (real_of_ereal (f x)) = f x"
    using ereal_real'
    by auto
  have "sum f X = sum f (X - {x}) + f x"
    using Suc \<open>x \<in> X\<close>
    by (metis add.commute sum.remove)
  also have "... = ereal (\<Sum>x \<in> X - {x}. real_of_ereal (f x)) + f x"
    using Suc card
    by simp
  also have "... = ereal (\<Sum>x \<in> X - {x}. real_of_ereal (f x)) + ereal (real_of_ereal (f x))"
    using eq
    by simp
  also have "... = ereal ((\<Sum>x \<in> X - {x}. real_of_ereal (f x)) + real_of_ereal (f x))"
    by simp
  also have 
    "... = ereal ((sum (real_of_ereal \<circ> f) (X - {x})) + real_of_ereal (f x))"
    using Suc
    by simp
  also have 
    "... = ereal (sum (real_of_ereal \<circ> f) X - (real_of_ereal \<circ> f) x + real_of_ereal (f x))"
    using sum_diff1[of X "real_of_ereal \<circ> f" x] \<open>x \<in> X\<close> Suc
    by metis
  also have "... = ereal (sum (real_of_ereal \<circ> f) X)"
    by simp
  also have "... = ereal (\<Sum>x\<in>X. real_of_ereal (f x))"
    by simp
  finally show ?case by satx
qed

text \<open>
The maximum of the characteristic function of a predicate is 1 iff there is 
at least one element satisfying the predicate, otherwise the maximum is 0.
\<close>
lemma char_helper: 
  fixes
    X :: "'x set" and \<phi> :: "'x \<Rightarrow> bool"
  assumes
    "X \<noteq> {}"
  shows
    "Max {characteristic \<phi> {True} x | x. x \<in> X} = 
      (if {x. x \<in> X \<and> \<phi> x} \<noteq> {} then 1::nat else 0::nat)"
proof -
  let ?all_zero = "\<forall>x \<in> X. characteristic \<phi> {True} x = 0" and
      ?ex_one = "\<exists>x \<in> X. characteristic \<phi> {True} x = 1" and
      ?ite = "if {x. x \<in> X \<and> \<phi> x} \<noteq> {} then 1::nat else 0::nat"
  have valued_01: "{characteristic \<phi> {True} x | x. x \<in> X} \<subseteq> {0, 1}"
    by auto
  moreover with this have fin: "finite {characteristic \<phi> {True} x | x. x \<in> X}"
    by (simp add: finite_subset)
  moreover have non_empty: "{characteristic \<phi> {True} x | x. x \<in> X} \<noteq> {}"
    using assms
    by simp
  ultimately have leq_1: "Max {characteristic \<phi> {True} x | x. x \<in> X} \<le> 1"
    using Max_in
    by auto
  have cases: "?all_zero \<or> ?ex_one"
    by auto
  moreover have max_0: "?all_zero \<longrightarrow> Max {characteristic \<phi> {True} x | x. x \<in> X} = 0"
    using assms Max_in[of "{characteristic \<phi> {True} x | x. x \<in> X}", OF fin non_empty]
    by fastforce (* TODO smaller steps? *)
  moreover have max_1: "?ex_one \<longrightarrow> Max {characteristic \<phi> {True} x | x. x \<in> X} = 1"
    using leq_1 Max_ge[OF fin, of 1]
    by force (* TODO smaller steps? *)
  ultimately have "\<exists>x \<in> X. characteristic \<phi> {True} x = Max {characteristic \<phi> {True} x | x. x \<in> X}"
    using assms
    by fastforce
  then obtain x :: 'x where "x \<in> X" and
    is_arg_max: "characteristic \<phi> {True} x = Max {characteristic \<phi> {True} x | x. x \<in> X}"
    by metis (* TODO use obtain_MAX lemma for infinite X instead? *)
  have "?ite = 1 \<longleftrightarrow> ({x. x \<in> X \<and> \<phi> x} \<noteq> {})"
    by presburger
  hence "?ite = 1 \<longleftrightarrow> (\<exists>x \<in> X. characteristic \<phi> {True} x = 1)"
    by auto
  hence "?ite = 1 \<longleftrightarrow> (\<exists>x \<in> X. characteristic \<phi> {True} x = 1)"
    by auto
  moreover have 
    "(\<exists>x \<in> X. characteristic \<phi> {True} x = 1) \<longrightarrow> (Max {characteristic \<phi> {True} x | x. x \<in> X} = 1)"
    using leq_1 Max_ge[OF fin, of 1]
    by force
  moreover have 
    "(Max {characteristic \<phi> {True} x | x. x \<in> X} = 1) \<longrightarrow> (characteristic \<phi> {True} x = 1)"
    using is_arg_max
    by metis
  moreover have "(characteristic \<phi> {True} x = 1) \<longrightarrow> (\<exists>x \<in> X. characteristic \<phi> {True} x = 1)"
    using \<open>x \<in> X\<close>
    by metis
  ultimately have eq_1: "?ite = 1 \<longleftrightarrow> (Max {characteristic \<phi> {True} x | x. x \<in> X} = 1)"
    by satx
  hence "?ite = 0 \<longleftrightarrow> (Max {characteristic \<phi> {True} x | x. x \<in> X} \<noteq> 1)"
    unfolding If_def
    by fastforce
  moreover have 
    "(Max {characteristic \<phi> {True} x | x. x \<in> X} \<noteq> 1) \<longleftrightarrow> 
      (Max {characteristic \<phi> {True} x | x. x \<in> X} = 0)"
    using cases max_0 max_1
    by linarith
  ultimately have eq_0: "?ite = 0 \<longleftrightarrow> (Max {characteristic \<phi> {True} x | x. x \<in> X} = 0)"
    by satx
  thus ?thesis
    using eq_1
    by presburger
qed

text \<open>
Mapping functions whose codomain contains exactly 2 elements to their preimage under one of 
these elements yields a bijection between the functions and the power set of their domain.
\<close>
lemma binary_map_preimg_bijection:
  fixes
    X :: "'x set" and Y :: "'y set" and y :: 'y
  assumes
    "card Y = 2" and "y \<in> Y"
  shows
    "bij_betw (\<lambda>f. preimg_in X f {y}) (actual_funcset X Y) (Pow X)"
proof (unfold bij_betw_def inj_on_def, safe)
  have "\<exists>y' \<in> Y. y' \<noteq> y"
    using assms is_singleton_altdef[of Y]
    unfolding is_singleton_def
    by auto
  then obtain y' :: 'y where "y' \<in> Y" and "y \<noteq> y'"
    by blast
  hence "{y', y} \<subseteq> Y"
    using assms
    by simp
  moreover have "card {y', y} = 2"
    using \<open>y \<noteq> y'\<close>
    by simp
  ultimately have elts: "Y = {y', y}"
    using card_subset_eq[of Y "{y', y}"] assms
    by fastforce
  {
    fix
      f :: "'x \<Rightarrow> 'y" and
      g :: "'x \<Rightarrow> 'y"
    assume
      fun_f: "f \<in> actual_funcset X Y" and 
      fun_g: "g \<in> actual_funcset X Y" and 
      preimg_eq: "preimg_in X f {y} = preimg_in X g {y}"
    hence ext: "\<forall>x. x \<notin> X \<longrightarrow> f x = g x"
      unfolding actual_funcset.simps extensional_def
      by simp
    have "\<exists>y' \<in> Y. y' \<noteq> y"
      using assms is_singleton_altdef[of Y]
      unfolding is_singleton_def
      by auto
    then obtain y' :: 'y where "y' \<in> Y" and "y \<noteq> y'"
      by blast
    hence "{y', y} \<subseteq> Y"
      using assms
      by simp
    moreover have "card {y', y} = 2"
      using \<open>y \<noteq> y'\<close>
      by simp
    ultimately have elts: "Y = {y', y}"
      using card_subset_eq[of Y "{y', y}"] assms
      by fastforce
    hence "\<forall>x \<in> X. (f x \<noteq> y \<longrightarrow> f x = y') \<and> (g x \<noteq> y \<longrightarrow> g x = y')"
      using fun_f fun_g
      by auto
    hence "\<forall>x \<in> X. (x \<notin> preimg_in X f {y} \<longrightarrow> (f x = y' \<and> g x = y'))"
      using preimg_eq
      unfolding preimg_in.simps
      by blast
    hence eq_not_y: "\<forall>x \<in> X. (x \<notin> preimg_in X f {y} \<longrightarrow> (f x = g x))"
      by metis
    moreover have eq_y: "\<forall>x \<in> X. (x \<in> preimg_in X f {y} \<longrightarrow> (f x = g x))"
      using preimg_eq
      by auto
    ultimately show "f = g"
      using ext
      by blast
  next
    fix x :: 'x and f :: "'x \<Rightarrow> 'y"
    assume "x \<in> preimg_in X f {y}"
    thus "x \<in> X"
      by simp
  next
    fix S :: "'x set"
    assume "S \<subseteq> X"
    let ?preimg_map = "\<lambda>x. (if x \<in> X then (if (x \<in> S) then y else y') else undefined)"
    have "?preimg_map \<in> actual_funcset X Y"
      unfolding actual_funcset.simps extensional_def Pi_def
      using elts
      by simp
    moreover have "S = preimg_in X ?preimg_map {y}"
      unfolding preimg_in.simps
      using \<open>y \<noteq> y'\<close> \<open>S \<subseteq> X\<close>
      by auto
    ultimately show "S \<in> (\<lambda>f. preimg_in X f {y}) ` actual_funcset X Y"
      by simp
  }
qed

text \<open>
If there is exactly one object that satisfies a predicate, 
then the set of objects satisfying the predicate has a cardinality of 1.
\<close>
lemma ex1_card1:
  fixes \<phi> :: "'x \<Rightarrow> bool"
  assumes "\<exists>!x. \<phi> x"
  shows "card {x. \<phi> x} = 1"
proof -
  from assms obtain x :: 'x where "\<phi> x" and "\<forall>y. y \<noteq> x \<longrightarrow> \<not> \<phi> y"
    by metis
  hence "{x. \<phi> x} = {x}"
    by auto
  thus ?thesis
    by simp
qed

section \<open>Equivalence of Block Axiom in SVGs and Voting Rules\<close>

theorem block_equivalence:
  "svg_rule_axiom_equivalence block_axiom_rule block_axiom_svg_on"
proof (unfold svg_rule_axiom_equivalence_def, safe)
  fix
    V :: "'a set" and B :: "'b set" and R :: "'c set" and f :: "('a \<Rightarrow> 'b) \<Rightarrow> 'c" 
    and ball1 :: 'b and  ball2 :: 'b and res1 :: 'c and res2 :: 'c
    and V' :: "'a set" and \<F> :: "'a set set" 
    and \<delta>1 :: "(('a, 'b, 'c) Voting_Rule, 'a) Voting_Power" 
    and \<delta>2 :: "('a Simple_Voting_Game, 'a) Voting_Power"
  assume
    equiv_model: "svg_rule_equivalence ball1 ball2 res1 res2 (V, B, R, f) (V', \<F>)" and
    equiv_power: "svg_rule_power_equivalence \<delta>1 \<delta>2" and
    sat_on_rules: "block_axiom_rule {(V, B, R, f)} \<delta>1"
  show "block_axiom_svg_on {(V', \<F>)} \<delta>2"
  proof (unfold block_axiom_svg_on.simps, safe)
    fix
      v :: 'a and w :: 'a and x :: 'a and V'' :: "'a set" and \<F>'' :: "'a set set"
    assume 
      vot_v: "v \<in> voters_svg (V', \<F>)" and vot_w: "w \<in> voters_svg (V', \<F>)" and "w \<noteq> v" and
      block: "block_svg (V', \<F>) (V'', \<F>'') v w x"
    have "V = V'"
      using equiv_model
      unfolding svg_rule_equivalence_def
      by simp
    hence "x \<notin> V"
      using block
      by simp
    have "x \<in> V''"
      using block
      by simp

    let ?f_block = "(V - {v,w} \<union> {x}, B, R, block_tally v w x f)"
        

    have is_block: "block_rule (V, B, R, f) ?f_block v w x"
      using \<open>x \<notin> V\<close>
      by simp
    hence geq_on_rules: "\<delta>1 ?f_block x \<ge> Max {\<delta>1 (V, B, R, f) v, \<delta>1 (V, B, R, f) w}"
      using sat_on_rules vot_v vot_w \<open>V = V'\<close>
      by simp

    have "\<exists>\<sigma>::'b \<Rightarrow> 'c. \<exists>r \<in> R. 
      bij_betw \<sigma> B R \<and> (\<forall>p. f p = r \<longleftrightarrow> preimg_in V p (preimg_in B \<sigma> {r}) \<in> \<F>)"
      using equiv_model
      unfolding svg_rule_equivalence_def
      by auto
    then obtain \<sigma> :: "'b \<Rightarrow> 'c" and r :: 'c where 
      res: "r \<in> R" and
      bij: "bij_betw \<sigma> B R" and 
      decision_corresp: "\<forall>p. f p = r \<longleftrightarrow> preimg_in V p (preimg_in B \<sigma> {r}) \<in> \<F>"
      by metis

    let ?voters_for_r = "\<lambda>p Votrs. preimg_in Votrs p (preimg_in B \<sigma> {r})"
  
    have "\<forall>p. block_tally v w x f p = r \<longleftrightarrow> f (block_profile v w x p) = r"
      by simp
    moreover have 
      "\<forall>p. f (block_profile v w x p) = r \<longleftrightarrow> ?voters_for_r (block_profile v w x p) V \<in> \<F>"
      using decision_corresp
      by metis
    moreover have
      "\<forall>p. ?voters_for_r (block_profile v w x p) V \<in> \<F> \<longleftrightarrow> ?voters_for_r p V'' \<in> \<F>''"
    proof (safe)
      fix p :: "'a \<Rightarrow> 'b"
      assume "?voters_for_r (block_profile v w x p) V \<in> \<F>"
      (* TODO show that either x is mapped to r or the other alternative  *)
      (* TODO first case: v and w are mapped to r *)
      (* TODO second case: v and w are mapped to the other alternative *)
      (* TODO both cases: p^{-1}(r) is winning *)
      show "?voters_for_r p V'' \<in> \<F>''"
        sorry
    next
      fix p :: "'a \<Rightarrow> 'b"
      assume "preimg_in V'' p (preimg_in B \<sigma> {r}) \<in> \<F>''"
      show "preimg_in V (block_profile v w x p) (preimg_in B \<sigma> {r}) \<in> \<F>"
        sorry
    qed
    ultimately have
      "\<forall>p. block_tally v w x f p = r \<longleftrightarrow> ?voters_for_r p V'' \<in> \<F>''"
      by metis
    hence "\<forall>p. rule ?f_block p = r \<longleftrightarrow> ?voters_for_r p (voters ?f_block) \<in> coalitions (V'', \<F>'')"
      using block \<open>V = V'\<close>
      by simp
    hence "\<exists>\<sigma>::'b \<Rightarrow> 'c. \<exists>r \<in> results ?f_block. bij_betw \<sigma> (ballots ?f_block) (results ?f_block) \<and>
      (\<forall>p. rule ?f_block p = r \<longleftrightarrow> 
      preimg_in (voters ?f_block) p (preimg_in (ballots ?f_block) \<sigma> {r}) \<in> (coalitions (V'', \<F>'')))"
      using bij res
      by auto
    moreover have "voters ?f_block = fst (V'', \<F>'')"
      using block \<open>V = V'\<close>
      by simp
    moreover have "ballots ?f_block = {ball1, ball2}"
      using equiv_model
      unfolding svg_rule_equivalence_def
      by simp
    moreover have "results ?f_block = {res1, res2}"
      using equiv_model
      unfolding svg_rule_equivalence_def
      by simp
    moreover have "ball1 \<noteq> ball2"
      using equiv_model
      unfolding svg_rule_equivalence_def
      by simp
    moreover have "res1 \<noteq> res2"
      using equiv_model
      unfolding svg_rule_equivalence_def
      by simp
    ultimately have equiv_model_block:
      "svg_rule_equivalence ball1 ball2 res1 res2 ?f_block (V'', \<F>'')"
      unfolding svg_rule_equivalence_def
      by metis
    hence "\<delta>2 (V'', \<F>'') x = \<delta>1 ?f_block x"
      using equiv_power \<open>x \<in> V''\<close>
      unfolding svg_rule_power_equivalence_def
      by fastforce
    moreover have "\<delta>1 (V, B, R, f) v = \<delta>2 (V', \<F>) v"
      using equiv_model equiv_power vot_v \<open>V = V'\<close>
      unfolding svg_rule_power_equivalence_def
      by fastforce
    moreover have "\<delta>1 (V, B, R, f) w = \<delta>2 (V', \<F>) w"
      using equiv_model equiv_power vot_w \<open>V = V'\<close>
      unfolding svg_rule_power_equivalence_def
      by fastforce
    ultimately show "Max {\<delta>2 (V', \<F>) v, \<delta>2 (V', \<F>) w} \<le> \<delta>2 (V'', \<F>'') x"
      using geq_on_rules
      by metis
  qed
next
  fix
    V :: "'a set" and B :: "'b set" and R :: "'c set" and f :: "('a \<Rightarrow> 'b) \<Rightarrow> 'c"
    and ball1 :: 'b and  ball2 :: 'b and res1 :: 'c and res2 :: 'c
    and V' :: "'a set" and \<F> :: "'a set set" 
    and \<delta>1 :: "(('a, 'b, 'c) Voting_Rule, 'a) Voting_Power" 
    and \<delta>2 :: "('a Simple_Voting_Game, 'a) Voting_Power"
  assume
    "svg_rule_equivalence ball1 ball2 res1 res2 (V, B, R, f) (V', \<F>)" and
    "svg_rule_power_equivalence \<delta>1 \<delta>2" and
    "block_axiom_svg_on {(V', \<F>)} \<delta>2"
  thus "block_axiom_rule {(V, B, R, f)} \<delta>1"
    sorry
qed

text \<open>
  On voting rules that correspond to simple voting games, 
  the Banzhaf indices on voting rules and SVGs behave the same.
\<close>
theorem banzhaf_equivalence:
  "svg_rule_power_equivalence banzhaf_rule_1 banzhaf_svg_1"
proof (unfold svg_rule_power_equivalence_def, safe)
  fix
    v :: 'a and V' :: "'a set" and \<F> :: "'a set set" and
    V :: "'a set" and B :: "'b set" and R :: "'c set" and f :: "('a \<Rightarrow> 'b) \<Rightarrow> 'c" and
    ball1 :: 'b and  ball2 :: 'b and res1 :: 'c and res2 :: 'c
  assume
    vot_v_rule: "v \<in> voters (V, B, R, f)" and
    vot_v_game: "v \<in> voters_svg (V', \<F>)" and
    equiv: "svg_rule_equivalence ball1 ball2 res1 res2 (V, B, R, f) (V', \<F>)"
  
\<comment> \<open>Basic Helpers\<close>
  hence eq_vot_set: "V = V'"
    unfolding svg_rule_equivalence_def
    by simp
  hence eq_card: "card V = card V'"
    by simp
  let ?n = "card V"
  have ballots_2: "B = {ball1, ball2} \<and> card B = 2"
    using equiv
    unfolding svg_rule_equivalence_def
    by simp
  have results_2: "R = {res1, res2} \<and> card R = 2"
    using equiv
    unfolding svg_rule_equivalence_def
    by simp
  have ex_fun: "actual_funcset V B \<noteq> {}"
    using ballots_2 exists_functions_1[of B]
    by auto

\<comment> \<open>Frequent Functions\<close>
  let ?profile = "\<lambda>f. f \<in> actual_funcset V B" and
      ?profiles = "actual_funcset V B" and
      ?diff_exactly_on = "\<lambda>v p q. p \<noteq> q \<and> differ_only_on v p q" and
      ?ballots_for = "\<lambda>r \<sigma>. preimg_in B \<sigma> {r}" and
      ?voters_choosing = "\<lambda>b p. preimg_in V p b" and
      ?results_differ = "\<lambda>p q. f p \<noteq> f q"
  let ?voters_for = "\<lambda>r p \<sigma>. ?voters_choosing (?ballots_for r \<sigma>) p"

\<comment> \<open>Ballot-Result Bijection\<close>
  obtain \<sigma> :: "'b \<Rightarrow> 'c" and r :: 'c where 
    "r \<in> R" and bij: "bij_betw \<sigma> B R" and decision_corresp: "\<forall>p. f p = r \<longleftrightarrow> ?voters_for r p \<sigma> \<in> \<F>"  
    using equiv  
    unfolding svg_rule_equivalence_def fst_def snd_def
    by fastforce

\<comment> \<open>Two Possible Results\<close>
  hence "card (R - {r}) = 1"
    using results_2
    by auto
  then obtain s :: 'c where "R - {r} = {s}"
    by (rule card_1_singletonE)
  hence res_set: "R = {s, r}"
    using \<open>r \<in> R\<close>    
    by auto
  moreover have "\<forall>p. f p \<in> R"
    sorry (* TODO currently does not hold, we need an assumption for that as well \<Rightarrow> locales? *)
  ultimately have neq_rewrite: "\<forall>p q. f p \<noteq> f q \<longleftrightarrow> \<not> (f p = r \<longleftrightarrow> f q = r)"
    using ballots_2
    by auto
  have "s \<in> R"
    using res_set
    by simp
  have "s \<noteq> r"
    using res_set results_2
    by auto
  have "?ballots_for r \<sigma> = {the_inv_into B \<sigma> r}"
    using bij \<open>r \<in> R\<close> preimg_the_inv[of r R \<sigma> B]
    by satx
  moreover have "?ballots_for s \<sigma> = {the_inv_into B \<sigma> s}"
    using bij \<open>s \<in> R\<close> preimg_the_inv[of s R \<sigma> B]
    by satx
  moreover have "the_inv_into B \<sigma> r \<noteq> the_inv_into B \<sigma> s"
    using bij \<open>s \<noteq> r\<close> bij \<open>r \<in> R\<close> \<open>s \<in> R\<close> f_the_inv_into_f bij_betw_def
    by metis
  moreover have "\<exists>x. x = the_inv_into B \<sigma> r"
    using bij
    by metis
  moreover have "\<exists>y. y = the_inv_into B \<sigma> s"
    using bij
    by metis

\<comment> \<open>Two Possible Ballots\<close>
  ultimately obtain x :: 'b and y :: 'b where 
    "x \<noteq> y" and x_r: "?ballots_for r \<sigma> = {x}" and y_s: "?ballots_for s \<sigma> = {y}"
    by metis
  hence part: "B = {x, y}"
    using bij \<open>R = {s, r}\<close>
    unfolding bij_betw_def
    by auto
  hence part': "\<forall>g. ?profile g \<longrightarrow> ?voters_choosing {x} g \<union> ?voters_choosing {y} g = V"
    unfolding actual_funcset.simps Pi_def
    by auto
  have swing_rewrite: 
    "\<forall>p q. (?profile p \<and> ?profile q \<and> ?diff_exactly_on v p q) \<longrightarrow>
      (((?voters_for r p \<sigma> \<in> \<F>) \<noteq> (?voters_for r q \<sigma> \<in> \<F>)) \<longleftrightarrow> 
        (swing_vote_svg \<F> v (?voters_for r p \<sigma>) = 1))" 
  proof (clarify)
    fix p :: "'a \<Rightarrow> 'b" and q :: "'a \<Rightarrow> 'b"
    assume "p \<noteq> q" and eq: "differ_only_on v p q" and 
      funcp: "p \<in> actual_funcset V B" and funcq: "q \<in> actual_funcset V B"
    let ?S = "preimg_in V p (preimg_in B \<sigma> {r})"
    let ?S' = "preimg_in V q (preimg_in B \<sigma> {r})"
    have "\<forall>w \<in> V - {v}. p w = q w"
      using eq
      by auto
    hence coinc: "\<forall>w \<in> V - {v}. w \<in> ?S \<longleftrightarrow> w \<in> ?S'"
      by simp
    have "p v \<noteq> q v"
      using eq \<open>p \<noteq> q\<close>
      by auto
    moreover have "\<forall>w \<in> V. p w = x \<or> p w = y"
      using part' preimg_in.simps funcp
      by auto
    moreover have "\<forall>w \<in> V. q w = x \<or> q w = y"
      using part' preimg_in.simps funcq
      by auto
    moreover have "v \<in> V"
      using vot_v_rule
      by simp
    ultimately have  "\<not> (p v = x \<longleftrightarrow> q v = x)"
      by metis
    hence "\<not> (v \<in> ?S \<longleftrightarrow> v \<in> ?S')"
      using x_r \<open>v \<in> V\<close>
      unfolding preimg_in.simps
      by auto
    hence "(?S' = ?S - {v} \<and> ?S = ?S \<union> {v}) \<or> (?S' = ?S \<union> {v} \<and> ?S = ?S - {v})"
      using coinc
      by auto
    hence 
      "((?S \<in> \<F>) \<noteq> (?S' \<in> \<F>)) \<longleftrightarrow> (swing_vote_svg \<F> v ?S = 1)"
      unfolding swing_vote_svg.simps
      by fastforce
    thus "((?S \<in> \<F>) \<noteq> (?S' \<in> \<F>)) = (swing_vote_svg \<F> v ?S = 1)"
      by satx
  qed

\<comment> \<open>Rewrite Banzhaf Indices\<close>
  show "banzhaf_rule_1 (V, B, R, f) v = banzhaf_svg_1 (V', \<F>) v"
  proof (cases "finite V")
    case False
    hence "banzhaf_rule_1 (V, B, R, f) v = 0"
      by simp
    moreover from False have "banzhaf_svg_1 (V', \<F>) v = 0"
      using eq_vot_set
      by simp
    ultimately show ?thesis
      by simp
  next
    case True
    let ?f = 
        "\<lambda>p. ereal 
          (if {q. ?profile q \<and> ?diff_exactly_on v p q \<and>
            (?voters_for r p \<sigma> \<in> \<F>) \<noteq> (?voters_for r q \<sigma> \<in> \<F>)} \<noteq> {} 
          then 1 else 0)" and
        ?g = 
          "\<lambda>p. ereal 
            (if {q. ?profile q \<and> ?diff_exactly_on v p q \<and>
              swing_vote_svg \<F> v (?voters_for r p \<sigma>) = 1} \<noteq> {} 
            then 1 else 0)" and
        ?swing = "\<lambda>p q. differ_only_on v p q \<and> ?results_differ p q"
    let ?max = 
          "\<lambda>p. ereal (Max {characteristic (?swing p) {True} q | q. ?profile q})" and
        ?ternary = 
          "\<lambda>p. ereal (if {q. ?profile q \<and> ?swing p q} \<noteq> {} then 1 else 0)"
    have rewrite_helper: "\<And>p. ?profile p \<Longrightarrow> ?max p = ?ternary p"
      using char_helper[of ?profiles "?swing _", OF ex_fun]
      by auto
    from True have rewrite_rule: 
      "banzhaf_rule_1 (V, B, R, f) v = (1 / 2^?n) * (\<Sum> p \<in> ?profiles. ?max p)"
      using ballots_2
      by auto
    also have "... = (1 / 2^?n) * (\<Sum> p \<in> ?profiles. ?ternary p)"
      using
        sum.cong[of ?profiles ?profiles ?max ?ternary, OF _ rewrite_helper]
      by metis
    also have "... = 
      (1 / 2^?n) * (\<Sum> p \<in> ?profiles. ereal 
        (if {q. ?profile q \<and> differ_only_on v p q \<and> (f p = r) \<noteq> (f q = r)} \<noteq> {} then 1 else 0))"
      using neq_rewrite
      by presburger
    also have "... = (1 / 2^?n) * (\<Sum> p \<in> ?profiles. ereal
        (if {q. q \<in> ?profiles \<and> differ_only_on v p q \<and>
          (?voters_for r p \<sigma> \<in> \<F>) \<noteq> (?voters_for r q \<sigma> \<in> \<F>)} \<noteq> {} 
        then 1 else 0))"
      using decision_corresp
      by simp
    also have "... = (1 / 2^?n) * (\<Sum> p \<in> ?profiles. ereal 
        (if {q. ?profile q \<and> ?diff_exactly_on v p q \<and>
          (?voters_for r p \<sigma> \<in> \<F>) \<noteq> (?voters_for r q \<sigma> \<in> \<F>)} \<noteq> {} 
        then 1 else 0))"
    proof -
      let ?f' = "\<lambda>p. ereal (if {q. q \<in> actual_funcset V B \<and> differ_only_on v p q \<and>
        (preimg_in V p (preimg_in B \<sigma> {r}) \<in> \<F>) \<noteq> (preimg_in V q (preimg_in B \<sigma> {r}) \<in> \<F>)} \<noteq> {} 
        then 1 else 0)"
      have "\<And>p. p \<in> actual_funcset V B \<Longrightarrow> 
        {q \<in> actual_funcset V B. differ_only_on v p q \<and>
          (preimg_in V p (preimg_in B \<sigma> {r}) \<in> \<F>) \<noteq> (preimg_in V q (preimg_in B \<sigma> {r}) \<in> \<F>)} 
        = {q \<in> actual_funcset V B. p \<noteq> q \<and> differ_only_on v p q \<and>
        (preimg_in V p (preimg_in B \<sigma> {r}) \<in> \<F>) \<noteq> (preimg_in V q (preimg_in B \<sigma> {r}) \<in> \<F>)}"
        by auto
      hence coinc: "\<And>p. p \<in> actual_funcset V B \<Longrightarrow> ?f' p = ?f p"
        by auto
      show ?thesis
        using sum.cong[of "actual_funcset V B" "actual_funcset V B" ?f' ?f, OF _ coinc]
        by metis
    qed
    also have "... = (1 / 2^?n) * (\<Sum> p \<in> ?profiles. ereal 
      (if {q. ?profile q \<and> ?diff_exactly_on v p q \<and>
        swing_vote_svg \<F> v (?voters_for r p \<sigma>) = 1} \<noteq> {} 
      then 1 else 0))"
    proof -
      have "\<And>p. p \<in> actual_funcset V B \<Longrightarrow> 
        (\<exists>q. (q \<in> actual_funcset V B \<and> p \<noteq> q \<and> differ_only_on v p q \<and>
          (preimg_in V p (preimg_in B \<sigma> {r}) \<in> \<F>) \<noteq> (preimg_in V q (preimg_in B \<sigma> {r}) \<in> \<F>)))
        = (\<exists>q. (q \<in> actual_funcset V B \<and> p \<noteq> q \<and> differ_only_on v p q \<and>
          (swing_vote_svg \<F> v (preimg_in V p (preimg_in B \<sigma> {r})) = 1)))"
        using swing_rewrite
        by metis
      hence "\<And>p. p \<in> actual_funcset V B \<Longrightarrow> 
        ({q. (q \<in> actual_funcset V B \<and> p \<noteq> q \<and> differ_only_on v p q \<and>
          (preimg_in V p (preimg_in B \<sigma> {r}) \<in> \<F>) \<noteq> (preimg_in V q (preimg_in B \<sigma> {r}) \<in> \<F>))} \<noteq> {})
        = ({q. (q \<in> actual_funcset V B \<and> p \<noteq> q \<and> differ_only_on v p q \<and>
          (swing_vote_svg \<F> v (preimg_in V p (preimg_in B \<sigma> {r})) = 1))} \<noteq> {})"
        by blast
      hence coinc: "\<And>p. p \<in> actual_funcset V B \<Longrightarrow> ?f p = ?g p"
        by presburger
      show ?thesis
        using sum.cong[of "actual_funcset V B" "actual_funcset V B" ?f ?g, OF _ coinc]
        by metis
    qed 
    also have "... = (1 / 2^?n) * 
      (\<Sum> p \<in> ?profiles. swing_vote_svg \<F> v (?voters_for r p \<sigma>))"
    proof -
      let ?h = "\<lambda>p. swing_vote_svg \<F> v (preimg_in V p (preimg_in B \<sigma> {r}))"
      have 
        "\<And>p. p \<in> actual_funcset V B \<Longrightarrow> 
          (\<exists>q. q \<in> actual_funcset V B \<and> p \<noteq> q \<and> differ_only_on v p q)"
        using ballots_2 vot_v_rule update_function[of v V B]
        by auto
      hence 
        "\<And>p. p \<in> actual_funcset V B \<Longrightarrow> 
          ({q \<in> actual_funcset V B. p \<noteq> q \<and> differ_only_on v p q \<and> 
          swing_vote_svg \<F> v (preimg_in V p (preimg_in B \<sigma> {r})) = 1} \<noteq> {}) \<longleftrightarrow> 
          (swing_vote_svg \<F> v (preimg_in V p (preimg_in B \<sigma> {r})) = 1)"
        by blast
      hence "\<And>p. p \<in> actual_funcset V B \<Longrightarrow> ?g p = ?h p"
        by simp
      thus ?thesis
        using sum.cong[of "actual_funcset V B" "actual_funcset V B" ?g ?h]
        by presburger
    qed
    also have 
      "... = (1 / 2^?n) * (\<Sum> S \<in> {?voters_for r p \<sigma> |p. ?profile p}. swing_vote_svg \<F> v S)"
    proof -
      have fin_func: "finite ?profiles"
        using True ballots_2 fin_funcset[of V B]
        by fastforce
      have "{?voters_for r p \<sigma> |p. ?profile p} \<subseteq> Pow V"
        by auto
      moreover have "finite (Pow V)"
        using True
        by simp
      ultimately have fin_preimg: 
        "finite {?voters_for r p \<sigma> |p. ?profile p}"
        by (rule finite_subset)
      have subset:
        "(\<lambda>p. ?voters_for r p \<sigma>) ` ?profiles \<subseteq> {?voters_for r p \<sigma> |p. ?profile p}"
        by auto
      have
        "\<And>S. S \<in> {preimg_in V p (preimg_in B \<sigma> {r}) |p. p \<in> actual_funcset V B} 
          \<Longrightarrow> (\<exists>! q \<in> actual_funcset V B. preimg_in V q (preimg_in B \<sigma> {r}) = S)"
        using ballots_2 binary_map_preimg_bijection[of B x V] x_r part
        unfolding bij_betw_def inj_on_def
        sorry (* would work when using OF "ballots_card_2" for the binary map theorem *)
      hence 
        "\<And>S. S \<in> {preimg_in V p (preimg_in B \<sigma> {r}) |p. p \<in> actual_funcset V B}
          \<Longrightarrow> of_nat (card {q \<in> actual_funcset V B. preimg_in V q (preimg_in B \<sigma> {r}) = S}) = 1"
        using ex1_card1[of "\<lambda>q. q \<in> actual_funcset V B \<and> preimg_in V q (preimg_in B \<sigma> {r}) = _"]
        by simp
      moreover have 
        "(\<Sum>p\<in>actual_funcset V B. 
            real_of_ereal (swing_vote_svg \<F> v (preimg_in V p (preimg_in B \<sigma> {r}))))
          = (\<Sum> S \<in> {preimg_in V p (preimg_in B \<sigma> {r}) |p. p \<in> actual_funcset V B}.
              of_nat (card {q \<in> actual_funcset V B. preimg_in V q (preimg_in B \<sigma> {r}) = S}) 
                        * real_of_ereal (swing_vote_svg \<F> v S))"
        using sum_fun_comp[
            of "actual_funcset V B" "{preimg_in V p (preimg_in B \<sigma> {r}) |p. p \<in> actual_funcset V B}" 
                "\<lambda>p. preimg_in V p (preimg_in B \<sigma> {r})" "\<lambda>S. real_of_ereal (swing_vote_svg \<F> v S)", 
            OF fin_func fin_preimg subset]
        by satx      
      ultimately have
        "(\<Sum>p\<in>actual_funcset V B. 
            real_of_ereal (swing_vote_svg \<F> v (preimg_in V p (preimg_in B \<sigma> {r}))))
          = (\<Sum>S\<in>{preimg_in V p (preimg_in B \<sigma> {r}) |p. p \<in> actual_funcset V B}.
              real_of_ereal (swing_vote_svg \<F> v S))"
        using sum.cong[of "{preimg_in V p (preimg_in B \<sigma> {r}) |p. p \<in> actual_funcset V B}"
            "{preimg_in V p (preimg_in B \<sigma> {r}) |p. p \<in> actual_funcset V B}"
            "\<lambda>S. of_nat (card {q \<in> actual_funcset V B. preimg_in V q (preimg_in B \<sigma> {r}) = S}) 
                    * real_of_ereal (swing_vote_svg \<F> v S)"
            "\<lambda>S. real_of_ereal (swing_vote_svg \<F> v S)"]
        using mult.commute mult.right_neutral real_ereal_1 real_of_ereal_mult
        by (metis (no_types, lifting))      
      moreover have 
        "... = (\<Sum>S \<in> {preimg_in V p (preimg_in B \<sigma> {r}) |p. p \<in> actual_funcset V B}. 
            (swing_vote_svg \<F> v S))"
        using ereal_sum[of 
            "{preimg_in V p (preimg_in B \<sigma> {r}) |p. p \<in> actual_funcset V B}" "swing_vote_svg \<F> v"]
        sorry (* TODO show preconditions of lemma *)
      moreover have 
        "(\<Sum>p\<in>actual_funcset V B. 
            real_of_ereal (swing_vote_svg \<F> v (preimg_in V p (preimg_in B \<sigma> {r}))))
        = (\<Sum>p \<in> actual_funcset V B. (swing_vote_svg \<F> v (preimg_in V p (preimg_in B \<sigma> {r}))))"
        using ereal_sum[of 
            "actual_funcset V B" "\<lambda>p. swing_vote_svg \<F> v (preimg_in V p (preimg_in B \<sigma> {r}))"]
        sorry (* TODO show preconditions of lemma *)
      ultimately show ?thesis
        by presburger
    qed
    also have "... = (1 / 2^?n) * (\<Sum> S \<in> Pow V. swing_vote_svg \<F> v S)"
      using bij ballots_2 results_2 preimg_funcset[of "?ballots_for r \<sigma>" B V] 
        sum.cong[of "{?voters_for r p \<sigma> |p. ?profile p}" "Pow V"]
      unfolding bij_betw_def inj_on_def
      sorry (* TODO show preconditions of lemma *)
    also have "... = banzhaf_svg_1 (V, \<F>) v"
      by simp
    finally show ?thesis
      using eq_vot_set
      by simp
  qed
qed

(* TODO characterize these voting rules independently of SVGs; Show that the set is non-empty *)
definition monotone_binary_voting_rules :: "('v, 'b, 'r) Voting_Rule set" where
  "monotone_binary_voting_rules = 
    {\<R> | \<R>. (\<exists>\<G> \<in> monotone_SVGs. \<exists>ball1 ball2 res1 res2. 
      svg_rule_equivalence ball1 ball2 res1 res2 \<R> \<G>)}"

(* Show that the voting rule Banzhaf index satisfies the block axiom 
by copying its proof from the SVG Banzhaf *)
theorem banzhaf_1_satisfies_block_axiom:
  "block_axiom_rule monotone_binary_voting_rules banzhaf_rule_1"
proof -
  have "\<forall>\<G> \<in> monotone_SVGs. block_axiom_svg_on {\<G>} banzhaf_svg_1"
    using banzhaf_1_satisfies_block_axiom
    by auto
  moreover have 
    "\<forall>\<R> \<in> monotone_binary_voting_rules. \<exists>\<G> \<in> monotone_SVGs. \<exists>ball1 ball2 res1 res2. 
      svg_rule_equivalence ball1 ball2 res1 res2 \<R> \<G>"
    unfolding monotone_binary_voting_rules_def
    by simp
  ultimately have "\<forall>\<R> \<in> monotone_binary_voting_rules. block_axiom_rule {\<R>} banzhaf_rule_1"
    using block_equivalence monotone_binary_voting_rules_def banzhaf_equivalence
    unfolding svg_rule_axiom_equivalence_def
    by fast
  thus ?thesis
    by simp
qed

*)

end