theory Voting_Power_Comparison
  imports Voting_Power_Scratch
          Simple_Voting_Game
          Voting_Rule

begin

section \<open>Locale Draft\<close>

(* 
Voting models as types of a typeclass: 
  class voting_model where
    voter_set :: "\<alpha> \<Rightarrow> 'v set" 
Problem: 'v is an additional type variable.
*)

(* Same thing as a locale: *)
locale voting_model = 
  fixes
    model_type :: "'\<alpha> itself" and 
      (* A specific voting system is represented by an object of type '\<alpha>  *)
    voter_set :: "'\<alpha> \<Rightarrow> 'v set"   
      (* Every voting model can be associated with a set of eligible/participating voters *)

(* The voting rule model represents voting systems via objects of type Voting_Rule *)
interpretation voting_rules: voting_model "TYPE(('v, 'b, 'r) Voting_Rule)" voters
proof - qed

(* The simple voting game model represents voting systems via objects of type Simple_Voting_Game *)
interpretation simple_voting_games: voting_model "TYPE('v Simple_Voting_Game)" fst
proof - qed

(* 
To compare two voting models, we fix them and a notion of two objects being equivalent, 
that is, representing the same voting system. We require that any two objects that represent
the same voting system are associated with the same set of eligible voters.  
*)
locale voting_model_comparison = 
  m1: voting_model "TYPE('\<alpha>)" voters1 + m2: voting_model "TYPE('\<beta>)" voters2 for voters1 voters2 +
  fixes
    model_equivalence :: "'\<alpha> \<Rightarrow> '\<beta> \<Rightarrow> bool"
  assumes
    equiv_imp_equal_voters: "\<forall>a b. model_equivalence a b \<longrightarrow> voters1 a = voters2 b"

(* 
A voting power index has as domain all pairs of voting model objects 
and (not necessarily) eligible voters.

We require that a voter who is not eligible in a given voting model object has power equal to 0.
*)
locale voting_power = voting_model "TYPE('\<alpha>)" voters for voters :: "'\<alpha> \<Rightarrow> 'v set" +
  fixes
    \<delta> :: "('\<alpha>, 'v) Voting_Power"
  assumes
    no_voter_no_power: "\<forall>a v. v \<notin> voters a \<longrightarrow> \<delta> a v = 0"

(* 
To compare two voting power indices, we fix them and a notion of voting model equivalence.
*)
locale voting_power_comparison = pow1: voting_power voters1 \<delta>1 + pow2: voting_power voters2 \<delta>2 
  + voting_model_comparison voters1 voters2 model_equivalence
  for voters1 \<delta>1 voters2 \<delta>2 and model_equivalence :: "'\<alpha> \<Rightarrow> '\<beta> \<Rightarrow> bool"
    (* TODO assumptions? *)
begin

(* 
The power indices at hand are equivalent iff they yield the same power for the same voter
in equivalent voting model objects. This represents the idea that a voter's actual power should
not depend on the voting model that is chosen to represent a voting system.
*)
definition power_equivalence :: bool where
  "power_equivalence = (\<forall>a b v. model_equivalence a b \<and> v \<in> voters1 a \<longrightarrow> \<delta>1 a v = \<delta>2 b v)"
  
end

section \<open>SVG-Voting-Rule-Definitions\<close>

fun preimg_in :: "'x set \<Rightarrow> ('x \<Rightarrow> 'y) \<Rightarrow> 'y set \<Rightarrow> 'x set" where
  "preimg_in X f Y = {x |x. x \<in> X \<and> f x \<in> Y}"

text \<open>
Ad hoc definition: A voting rule is equivalent to an SVG G if it "behaves like the SVG".
For this to be the case, the voting rule must have exactly two possible ballots,
two possible results and there must be a bijection between ballots and results that yields a notion
of "voting for a specific result" (by voting for its corresponding ballot).
Given this bijection, there must be a distinguished result that corresponds to the "yes" option
in the SVG G.
\<close>
definition svg_rule_equivalence :: 
  "('v, 'b, 'r) Voting_Rule \<Rightarrow> 'v Simple_Voting_Game \<Rightarrow> bool" where
  "svg_rule_equivalence \<R> \<G> = (
    voters \<R> = fst \<G> \<and>
    card (ballots \<R>) = 2 \<and> 
    card (results \<R>) = 2 \<and> 
    (\<exists>\<sigma>::'b \<Rightarrow> 'r. \<exists>r \<in> results \<R>. bij_betw \<sigma> (ballots \<R>) (results \<R>) \<and>
      (\<forall>p. rule \<R> p = r \<longleftrightarrow> preimg_in (voters \<R>) p (preimg_in (ballots \<R>) \<sigma> {r}) \<in> (coalitions \<G>))
    )
  )"

locale rule_simple_voting_game_comparison =
  comp: voting_model_comparison voters fst svg_rule_equivalence
begin

(* Transform voting rules to an equivalent SVG *)
fun transform_rule :: "('a, 'b, 'c) Voting_Rule \<Rightarrow> 'a Simple_Voting_Game" 
  where "transform_rule (V, B, R, f) = (V, {})" (* TODO *)

(* Why undefined constant?:
lemma "comp.model_equivalence rule (transform_rule rule)" *)

end

(* Show that the given equivalence function for SVGs and voting rules is a valid comparison map *)
sublocale 
  rule_simple_voting_game_comparison \<subseteq> voting_model_comparison voters fst svg_rule_equivalence
  by (unfold_locales, unfold svg_rule_equivalence_def, simp)

text \<open>
Ad hoc definition: A voting power index formulated on the domain of voting rules is equivalent
to a voting power index on the domain of SVGs if they yield the same power given equivalent inputs.
\<close>
definition svg_rule_power_equivalence ::
  "(('v, 'b, 'r) Voting_Rule, 'v) Voting_Power \<Rightarrow> ('v Simple_Voting_Game, 'v) Voting_Power \<Rightarrow> bool"
  where 
    "svg_rule_power_equivalence \<delta>1 \<delta>2 = (
      \<forall>\<R> \<G>. svg_rule_equivalence \<R> \<G> \<longrightarrow> (\<forall>v \<in> voters \<R> \<inter> fst \<G>. \<delta>1 \<R> v = \<delta>2 \<G> v)
    )"

text \<open>
Ad hoc definition: Two voting power axioms, where one is formulated on the domain of SVG voting
power indices and the other is defined on the domain of voting rule power indices, are equivalent
if they yield the same truth values on equivalent inputs.
\<close>
definition svg_rule_axiom_equivalence ::
  "(('v, 'b, 'r) Voting_Rule, 'v) Voting_Power_Axiom \<Rightarrow> 
    ('v Simple_Voting_Game, 'v) Voting_Power_Axiom \<Rightarrow> bool" where
  "svg_rule_axiom_equivalence \<phi>1 \<phi>2 = (\<forall>m1 m2 \<delta>1 \<delta>2. 
    svg_rule_equivalence m1 m2 \<and> svg_rule_power_equivalence \<delta>1 \<delta>2 \<longrightarrow> (\<phi>1 {m1} \<delta>1 \<longleftrightarrow> \<phi>2 {m2} \<delta>2))"


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
    and V' :: "'a set" and \<F> :: "'a set set" 
    and \<delta>1 :: "(('a, 'b, 'c) Voting_Rule, 'a) Voting_Power" 
    and \<delta>2 :: "('a Simple_Voting_Game, 'a) Voting_Power"
  assume
    equiv_model: "svg_rule_equivalence (V, B, R, f) (V', \<F>)" and
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

    let ?f_block = "(V - {v,w} \<union> {x}, B, R, f)"

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
    moreover have
      "\<forall>p. (preimg_in V p (preimg_in B \<sigma> {r}) \<in> \<F>) \<longleftrightarrow> (preimg_in V'' p (preimg_in B \<sigma> {r}) \<in> \<F>'')"
      sorry (* TODO does this even hold? *)
    moreover have "voters ?f_block = fst (V'', \<F>'')"
      using block \<open>V = V'\<close>
      by simp
    moreover have "card (ballots ?f_block) = 2"
      using equiv_model
      unfolding svg_rule_equivalence_def
      by simp
    moreover have "card (results ?f_block) = 2"
      using equiv_model
      unfolding svg_rule_equivalence_def
      by simp
    ultimately have equiv_model_block:"svg_rule_equivalence ?f_block (V'', \<F>'')"
      unfolding svg_rule_equivalence_def
      by force
    hence "\<delta>2 (V'', \<F>'') x = \<delta>1 ?f_block x"
      using equiv_power \<open>x \<in> V''\<close>
      unfolding svg_rule_power_equivalence_def
      by simp
    moreover have "\<delta>1 (V, B, R, f) v = \<delta>2 (V', \<F>) v"
      using equiv_model equiv_power vot_v \<open>V = V'\<close>
      unfolding svg_rule_power_equivalence_def
      by simp
    moreover have "\<delta>1 (V, B, R, f) w = \<delta>2 (V', \<F>) w"
      using equiv_model equiv_power vot_w \<open>V = V'\<close>
      unfolding svg_rule_power_equivalence_def
      by simp
    ultimately show "Max {\<delta>2 (V', \<F>) v, \<delta>2 (V', \<F>) w} \<le> \<delta>2 (V'', \<F>'') x"
      using geq_on_rules
      by metis
  qed
next
  fix
    V :: "'a set" and B :: "'b set" and R :: "'c set" and f :: "('a \<Rightarrow> 'b) \<Rightarrow> 'c"
    and V' :: "'a set" and \<F> :: "'a set set" 
    and \<delta>1 :: "(('a, 'b, 'c) Voting_Rule, 'a) Voting_Power" 
    and \<delta>2 :: "('a Simple_Voting_Game, 'a) Voting_Power"
  assume
    "svg_rule_equivalence (V, B, R, f) (V', \<F>)" and
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
    V :: "'a set" and B :: "'b set" and R :: "'c set" and f :: "('a \<Rightarrow> 'b) \<Rightarrow> 'c"
  assume
    vot_v_rule: "v \<in> voters (V, B, R, f)" and
    vot_v_game: "v \<in> voters_svg (V', \<F>)" and
    equiv: "svg_rule_equivalence (V, B, R, f) (V', \<F>)"
  
\<comment> \<open>Basic Helpers\<close>
  hence eq_vot_set: "V = V'"
    unfolding svg_rule_equivalence_def
    by simp
  hence eq_card: "card V = card V'"
    by simp
  let ?n = "card V"
  have ballots_2: "card B = 2"
    using equiv
    unfolding svg_rule_equivalence_def
    by simp
  have results_2: "card R = 2"
    using equiv
    unfolding svg_rule_equivalence_def
    by simp
  have ex_fun: "actual_funcset V B \<noteq> {}"
    using ballots_2 exists_functions_1[of B]
    by fastforce

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
    by auto

\<comment> \<open>Two Possible Results\<close>
  hence "card (R - {r}) = 1"
    using results_2
    by simp
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
      by simp
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
        using binary_map_preimg_bijection[of B x V, OF ballots_2] x_r part
        unfolding bij_betw_def inj_on_def
        by auto
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
  "monotone_binary_voting_rules = {\<R> | \<R>. (\<exists>\<G> \<in> monotone_SVGs. svg_rule_equivalence \<R> \<G>)}"

(* Show that the voting rule Banzhaf index satisfies the block axiom 
by copying its proof from the SVG Banzhaf *)
theorem banzhaf_1_satisfies_block_axiom:
  "block_axiom_rule monotone_binary_voting_rules banzhaf_rule_1"
proof -
  have "\<forall>\<G> \<in> monotone_SVGs. block_axiom_svg_on {\<G>} banzhaf_svg_1"
    using banzhaf_1_satisfies_block_axiom
    by auto
  hence "\<forall>\<R> \<in> monotone_binary_voting_rules. block_axiom_rule {\<R>} banzhaf_rule_1"
    using block_equivalence monotone_binary_voting_rules_def banzhaf_equivalence
    unfolding svg_rule_axiom_equivalence_def
    by blast
  thus ?thesis
    by simp
qed

end