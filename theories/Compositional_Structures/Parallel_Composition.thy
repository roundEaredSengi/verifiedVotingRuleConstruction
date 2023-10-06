(*  File:       Parallel_Composition.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Parallel Composition\<close>

theory Parallel_Composition
  imports "Basic_Modules/Component_Types/Aggregator"
          "Basic_Modules/Component_Types/Electoral_Module"
begin

text \<open>
  The parallel composition composes a new electoral module from
  two electoral modules combined with an aggregator.
  Therein, the two modules each make a decision and the aggregator combines
  them to a single (aggregated) result.
\<close>

subsection \<open>Definition\<close>

fun parallel_composition :: "('a, 'v, 'a Result) Electoral_Module \<Rightarrow> 
        ('a, 'v, 'a Result) Electoral_Module \<Rightarrow>
        'a Aggregator \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module" where
  "parallel_composition m n agg V A p = agg A (m V A p) (n V A p)"

abbreviation parallel :: "('a, 'v, 'a Result) Electoral_Module \<Rightarrow> 'a Aggregator \<Rightarrow>
        ('a, 'v, 'a Result) Electoral_Module \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module"
      ("_ \<parallel>\<^sub>_ _" [50, 1000, 51] 50) where
  "m \<parallel>\<^sub>a n == parallel_composition m n a"

subsection \<open>Soundness\<close>

theorem par_comp_sound[simp]:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    n :: "('a, 'v, 'a Result) Electoral_Module" and
    a :: "'a Aggregator"
  assumes
    "social_choice_result.electoral_module m" and
    "social_choice_result.electoral_module n" and
    "aggregator a"
  shows "social_choice_result.electoral_module (m \<parallel>\<^sub>a n)"
proof (unfold social_choice_result.electoral_module_def, safe)
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assume
    "finite A" and
    "finite V" and
    "profile V A p"
  moreover have
    "\<forall> a'. aggregator a' =
      (\<forall> A' e r d e' r' d'.
        (well_formed (A'::'a set) (e, r', d) \<and> well_formed A' (r, d', e')) \<longrightarrow>
          well_formed A' (a' A' (e, r', d) (r, d', e')))"
    unfolding aggregator_def
    by blast
  moreover have
    "\<forall> m' V' A' p'.
      (social_choice_result.electoral_module m' \<and> finite (A'::'a set) 
        \<and> finite (V'::'v set) \<and> profile V' A' p') \<longrightarrow> well_formed A' (m' V' A' p')"
    using par_comp_result_sound
    by (metis (no_types))
  ultimately have "well_formed A (a A (m V A p) (n V A p))"
    using combine_ele_rej_def assms
    by metis
  thus "well_formed A ((m \<parallel>\<^sub>a n) V A p)"
    by simp
qed

subsection \<open>Composition Rule\<close>

text \<open>
  Using a conservative aggregator, the parallel composition
  preserves the property non-electing.
\<close>

theorem conserv_agg_presv_non_electing[simp]:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    n :: "('a, 'v, 'a Result) Electoral_Module" and
    a :: "'a Aggregator"
  assumes
    non_electing_m: "non_electing m" and
    non_electing_n: "non_electing n" and
    conservative: "agg_conservative a"
  shows "non_electing (m \<parallel>\<^sub>a n)"
proof (unfold non_electing_def, safe)
  have "social_choice_result.electoral_module m"
    using non_electing_m
    unfolding non_electing_def
    by simp
  moreover have "social_choice_result.electoral_module n"
    using non_electing_n
    unfolding non_electing_def
    by simp
  moreover have "aggregator a"
    using conservative
    unfolding agg_conservative_def
    by simp
  ultimately show "social_choice_result.electoral_module (m \<parallel>\<^sub>a n)"
    using par_comp_sound
    by simp
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    w :: "'a"
  assume
    fin_A: "finite A" and 
    fin_V: "finite V" and
    prof_A: "profile V A p" and
    w_wins: "w \<in> elect V (m \<parallel>\<^sub>a n) A p"
  have emod_m: "social_choice_result.electoral_module m"
    using non_electing_m
    unfolding non_electing_def
    by simp
  have emod_n: "social_choice_result.electoral_module n"
    using non_electing_n
    unfolding non_electing_def
    by simp
  have "\<forall> r r' d d' e e' A' f.
          ((well_formed (A'::'a set) (e', r', d') \<and> well_formed A' (e, r, d)) \<longrightarrow>
            elect_r (f A' (e', r', d') (e, r, d)) \<subseteq> e' \<union> e \<and>
              reject_r (f A' (e', r', d') (e, r, d)) \<subseteq> r' \<union> r \<and>
              defer_r (f A' (e', r', d') (e, r, d)) \<subseteq> d' \<union> d) =
                ((well_formed A' (e', r', d') \<and> well_formed A' (e, r, d)) \<longrightarrow>
                  elect_r (f A' (e', r', d') (e, r, d)) \<subseteq> e' \<union> e \<and>
                    reject_r (f A' (e', r', d') (e, r, d)) \<subseteq> r' \<union> r \<and>
                    defer_r (f A' (e', r', d') (e, r, d)) \<subseteq> d' \<union> d)"
    by linarith
  hence "\<forall> a'. agg_conservative a' =
          (aggregator a' \<and>
            (\<forall> A' e e' d d' r r'.
              (well_formed (A'::'a set) (e, r, d) \<and> well_formed A' (e', r', d')) \<longrightarrow>
                elect_r (a' A' (e, r, d) (e', r', d')) \<subseteq> e \<union> e' \<and>
                  reject_r (a' A' (e, r, d) (e', r', d')) \<subseteq> r \<union> r' \<and>
                  defer_r (a' A' (e, r, d) (e', r', d')) \<subseteq> d \<union> d'))"
    unfolding agg_conservative_def
    by simp
  hence "aggregator a \<and>
          (\<forall> A' e e' d d' r r'.
            (well_formed A' (e, r, d) \<and> well_formed A' (e', r', d')) \<longrightarrow>
              elect_r (a A' (e, r, d) (e', r', d')) \<subseteq> e \<union> e' \<and>
                reject_r (a A' (e, r, d) (e', r', d')) \<subseteq> r \<union> r' \<and>
                defer_r (a A' (e, r, d) (e', r', d')) \<subseteq> d \<union> d')"
    using conservative
    by presburger
  hence "let c = (a A (m V A p) (n V A p)) in
          (elect_r c \<subseteq> ((elect V m A p) \<union> (elect V n A p)))"
    using emod_m emod_n fin_A fin_V par_comp_result_sound
          prod.collapse prof_A
    by metis
  hence "w \<in> ((elect V m A p) \<union> (elect V n A p))"
    using w_wins
    by auto
  thus "w \<in> {}"
    using sup_bot_right fin_A fin_V prof_A
          non_electing_m non_electing_n
    unfolding non_electing_def
    by (metis (no_types, lifting))
qed

end
