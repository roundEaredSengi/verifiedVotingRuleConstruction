theory Voting_Power_Comparison
  imports Voting_Power_Scratch
          Simple_Voting_Game
          Voting_Rule

begin

section \<open>Locale Draft\<close>

(*
locale Voting_Model_Comparison =
  fixes
    model_similarity :: "'x \<Rightarrow> 'y \<Rightarrow> bool"

locale Voting_Power_Comparison =
  fixes 
    delta1 :: "('x, 'v) Voting_Power" and
    delta2 :: "('y, 'v) Voting_Power" and
    similarity :: "('x, 'v) Voting_Power \<Rightarrow> ('y, 'v) Voting_Power \<Rightarrow> bool"
  assumes
    "similarity delta1 delta2"

definition (in Voting_Model_Comparison) numerical_similarity :: 
  "('x, 'v) Voting_Power \<Rightarrow> ('y, 'v) Voting_Power \<Rightarrow> bool" where
  "numerical_similarity delta1 delta2 = (\<forall>m1 m2. model_similarity m1 m2 \<longrightarrow> (\<forall>v. delta1 m1 v = delta2 m2 v))"

locale Numerical_Voting_Power_Comparison = 
    model_comp: Voting_Model_Comparison model_similarity + 
    power_comp: Voting_Power_Comparison delta1 delta2 model_comp.numerical_similarity 
    for model1 and model2 and model_similarity and delta1 and delta2
begin

thm power_comp.Voting_Power_Comparison_axioms

end 
*)

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
    "svg_rule_equivalence (V, B, R, f) (V', \<F>)" and
    "svg_rule_power_equivalence \<delta>1 \<delta>2" and
    "block_axiom_rule {(V, B, R, f)} \<delta>1"
  show "block_axiom_svg_on {(V', \<F>)} \<delta>2"
  proof (unfold block_axiom_svg_on.simps, safe)
    fix
      v :: 'a and w :: 'a and x :: 'a and V'' :: "'a set" and \<F>'' :: "'a set set"
    assume 
      "v \<in> voters_svg (V', \<F>)" and "w \<in> voters_svg (V', \<F>)" and "w \<noteq> v" and
      block: "block_svg (V', \<F>) (V'', \<F>'') v w x"
    (* TODO: Define the voting rule f' that is equivalent to (V'', \<F>'') *)
    (* TODO: Show that f' is a block_rule of (V, B, R, f) *)
    (* TODO: Apply rule block axiom *)
    (* TODO: Apply equivalence to deduce goal *)
    show "Max {\<delta>2 (V', \<F>) v, \<delta>2 (V', \<F>) w} \<le> \<delta>2 (V'', \<F>'') x"
      sorry
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

\<comment> \<open>Helpers\<close>
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
  obtain \<sigma> :: "'b \<Rightarrow> 'c" and r :: 'c where
    "r \<in> R" and bij: "bij_betw \<sigma> B R" and 
    decision_corresp: "\<forall>p. f p = r \<longleftrightarrow> preimg_in V p (preimg_in B \<sigma> {r}) \<in> \<F>"  
    using equiv  
    unfolding svg_rule_equivalence_def fst_def snd_def
    by auto
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
  have "preimg_in B \<sigma> {r} = {the_inv_into B \<sigma> r}"
    using bij \<open>r \<in> R\<close> preimg_the_inv[of r R \<sigma> B]
    by satx
  moreover have "preimg_in B \<sigma> {s} = {the_inv_into B \<sigma> s}"
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
  ultimately obtain x :: 'b and y :: 'b where 
    "x \<noteq> y" and x_r: "preimg_in B \<sigma> {r} = {x}" and y_s: "preimg_in B \<sigma> {s} = {y}"
    by metis
  hence part: "B = {x, y}"
    using bij \<open>R = {s, r}\<close>
    unfolding bij_betw_def
    by auto
  hence part': "\<forall>g \<in> actual_funcset V B. 
    preimg_in V g {x} \<union> preimg_in V g {y} = V"
    unfolding actual_funcset.simps Pi_def
    by auto
  have swing_rewrite: "\<forall>p q. 
    (p \<in> actual_funcset V B \<and> q \<in> actual_funcset V B \<and> p \<noteq> q \<and> differ_only_on v p q) \<longrightarrow>
    ((preimg_in V p (preimg_in B \<sigma> {r}) \<in> \<F>) \<noteq> (preimg_in V q (preimg_in B \<sigma> {r}) \<in> \<F>)
    \<longleftrightarrow> (swing_vote_svg \<F> v (preimg_in V p (preimg_in B \<sigma> {r})) = 1))" 
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

\<comment> \<open>Rewrite power indices\<close>
  show "banzhaf_rule_1 (V, B, R, f) v = banzhaf_svg_1 (V', \<F>) v"
  proof (cases "finite V")
    case True
    let ?f = "\<lambda>p. ereal (if {q. q \<in> actual_funcset V B \<and> p \<noteq> q \<and> differ_only_on v p q \<and>
          (preimg_in V p (preimg_in B \<sigma> {r}) \<in> \<F>) \<noteq> (preimg_in V q (preimg_in B \<sigma> {r}) \<in> \<F>)} \<noteq> {} 
          then 1 else 0)" and
        ?g = "\<lambda>p. ereal( if {q. q \<in> actual_funcset V B \<and> p \<noteq> q \<and> differ_only_on v p q \<and>
          swing_vote_svg \<F> v (preimg_in V p (preimg_in B \<sigma> {r})) = 1} \<noteq> {} 
          then 1 else 0)" and
        ?\<phi> = "\<lambda>p q. differ_only_on v p q \<and> f p \<noteq> f q"
    let ?max = "\<lambda>p. ereal (Max {characteristic (?\<phi> p) {True} q | q. q \<in> actual_funcset V B})" and
        ?ternary = "\<lambda>p. ereal (if {q \<in> actual_funcset V B. ?\<phi> p q} \<noteq> {} then 1 else 0)"
    have rewrite_helper: "\<And>p. p \<in> actual_funcset V B \<Longrightarrow> ?max p = ?ternary p"
      using char_helper[of "actual_funcset V B" "?\<phi> _", OF ex_fun]
      by auto
    from True have rewrite_rule: 
      "banzhaf_rule_1 (V, B, R, f) v = (1 / 2^?n) * (\<Sum> p \<in> actual_funcset V B. ?max p)"
      using ballots_2
      by simp
    also have "... = (1 / 2^?n) * (\<Sum> p \<in> actual_funcset V B. ?ternary p)"
      using
        sum.cong[of "actual_funcset V B" "actual_funcset V B" ?max ?ternary, OF _ rewrite_helper]
      by metis
    also have "... = (1 / 2^?n) * (\<Sum> p \<in> actual_funcset V B. 
      ereal (if {q. q \<in> actual_funcset V B \<and> differ_only_on v p q \<and> (f p = r) \<noteq> (f q = r)} \<noteq> {} 
        then 1 else 0))"
      using neq_rewrite
      by presburger
    also have "... = (1 / 2^?n) * (\<Sum> p \<in> actual_funcset V B. 
      ereal( if {q. q \<in> actual_funcset V B \<and> differ_only_on v p q \<and>
        (preimg_in V p (preimg_in B \<sigma> {r}) \<in> \<F>) \<noteq> (preimg_in V q (preimg_in B \<sigma> {r}) \<in> \<F>)} \<noteq> {} 
        then 1 else 0))"
      using decision_corresp
      by simp
    also have "... = (1 / 2^?n) * (\<Sum> p \<in> actual_funcset V B. 
      ereal (if {q. q \<in> actual_funcset V B \<and> p \<noteq> q \<and> differ_only_on v p q \<and>
        (preimg_in V p (preimg_in B \<sigma> {r}) \<in> \<F>) \<noteq> (preimg_in V q (preimg_in B \<sigma> {r}) \<in> \<F>)} \<noteq> {} 
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
    also have "... = (1 / 2^?n) * (\<Sum> p \<in> actual_funcset V B. 
      ereal (if {q. q \<in> actual_funcset V B \<and> p \<noteq> q \<and> differ_only_on v p q \<and>
        swing_vote_svg \<F> v (preimg_in V p (preimg_in B \<sigma> {r})) = 1} \<noteq> {} 
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
      (\<Sum> p \<in> actual_funcset V B. swing_vote_svg \<F> v (preimg_in V p (preimg_in B \<sigma> {r})))"
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
    also have "... = (1 / 2^?n) * 
      (\<Sum> S \<in> {preimg_in V p (preimg_in B \<sigma> {r}) |p. p \<in> actual_funcset V B}. swing_vote_svg \<F> v S)"
    proof -
      have fin_func: "finite (actual_funcset V B)"
        using True ballots_2 fin_funcset[of V B]
        by fastforce
      have "{preimg_in V p (preimg_in B \<sigma> {r}) |p. p \<in> actual_funcset V B} \<subseteq> Pow V"
        by auto
      moreover have "finite (Pow V)"
        using True
        by simp
      ultimately have fin_preimg: 
        "finite {preimg_in V p (preimg_in B \<sigma> {r}) |p. p \<in> actual_funcset V B}"
        by (rule finite_subset)
      have subset:
        "(\<lambda>p. preimg_in V p (preimg_in B \<sigma> {r})) ` actual_funcset V B
          \<subseteq> {preimg_in V p (preimg_in B \<sigma> {r}) |p. p \<in> actual_funcset V B}"
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
      using bij ballots_2 results_2 preimg_funcset[of "preimg_in B \<sigma> {r}" B V] 
        sum.cong[of "{preimg_in V p (preimg_in B \<sigma> {r}) |p. p \<in> actual_funcset V B}" "Pow V"]
      unfolding bij_betw_def inj_on_def
      sorry (* TODO show preconditions of lemma *)
    also have "... = banzhaf_svg_1 (V, \<F>) v"
      by simp
    finally show ?thesis
      using eq_vot_set
      by simp
  next
    case False
    hence "banzhaf_rule_1 (V, B, R, f) v = 0"
      by simp
    moreover from False have "banzhaf_svg_1 (V', \<F>) v = 0"
      using eq_vot_set
      by simp
    ultimately show ?thesis
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
    by simp
  hence "\<forall>\<R> \<in> monotone_binary_voting_rules. block_axiom_rule {\<R>} banzhaf_rule_1"
    using block_equivalence monotone_binary_voting_rules_def banzhaf_equivalence
    unfolding svg_rule_axiom_equivalence_def
    by blast
  thus ?thesis
    by simp
qed

end