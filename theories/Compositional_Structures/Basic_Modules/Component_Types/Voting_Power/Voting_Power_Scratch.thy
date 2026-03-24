theory Voting_Power_Scratch
  imports "HOL-Library.Extended_Nonnegative_Real"
          "HOL-Probability.Probability_Measure"
          "../Voting_Models/Voting_Model_Scratch"

begin

section \<open>Basic Definitions and Types\<close>

type_synonym ('x, 'v) Voting_Power = "'x \<Rightarrow> 'v \<Rightarrow> ereal"
type_synonym ('x, 'v) Voting_Power_Axiom = "'x set \<Rightarrow> ('x, 'v) Voting_Power \<Rightarrow> bool"

section \<open>Auxiliary Definitions and Lemmas\<close>

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
  

end