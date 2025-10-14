section \<open>Voting Model Comparison\<close>

theory Voting_Model_Comparison
  imports "Games/Simple_Voting_Game"

begin

locale svg_rule_power_comparison = 
  equiv: power_equivalence \<V> "(UNIV::bool set)" "(UNIV::bool set)" \<M> \<M>' isomorphism \<delta> \<delta>' AN AN'
  for 
    \<V> :: "'v set" and
    \<M> :: "((('v \<Rightarrow> bool) \<Rightarrow> bool) \<times> (('v \<Rightarrow> bool) \<Rightarrow> bool)) set" and
    \<M>' :: "('v Simple_Voting_Game \<times> (('v \<Rightarrow> bool) \<Rightarrow> bool)) set" and
    isomorphism :: "(('v \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> 'v Simple_Voting_Game \<Rightarrow> bool" and
    \<delta> :: "('v, ('v \<Rightarrow> bool) \<Rightarrow> bool) Voting_Power" and
    \<delta>' :: "('v, 'v Simple_Voting_Game) Voting_Power" and
    AN :: "('v, 'b, 'o, ('v \<Rightarrow> bool) \<Rightarrow> bool) abstract_notions" and
    AN' :: "('v, 'b, 'o, 'v Simple_Voting_Game) abstract_notions" +
  assumes
    rules: "\<forall> (m, f) \<in> \<M>. voting_rule \<V> (UNIV::bool set) (UNIV::bool set) m" and (* and m = f? *)
    games: "\<forall> (m', f') \<in> \<M>'. simple_voting_game \<V> m'"
begin

text \<open>
  Assuming equivalence of \<delta> on voting rules and \<delta>' on simple voting games, 
  they both either satisfy or do not satisfy the null player axiom.
  Thus, equivalence of the null player axiom is necessary for \<delta> and \<delta>' to be equivalent.
\<close>
lemma equiv_null_player: 
  "equiv.pow1.null_player \<longleftrightarrow> equiv.pow2.null_player"
proof (unfold equiv.pow1.null_player_def equiv.pow2.null_player_def, safe)
  fix
    V :: "'v set" and
    vf :: "'v set \<Rightarrow> bool" and
    f :: " ('v \<Rightarrow> bool) \<Rightarrow> bool" and
    v :: 'v
  assume
    valid_game: "((V, vf), f) \<in> \<M>'" and
    voter: "v \<in> \<V>" and
    np: "\<not> has_swing_vote AN' (V, vf) v" and
    np_ax: "\<forall>(m, f) \<in> \<M>. \<forall>v \<in> \<V>. \<not> has_swing_vote AN m v \<longrightarrow> \<delta> m v = 0"
  interpret game: simple_voting_game \<V> "(V, vf)"
    using games valid_game
    by blast
  have "\<forall>(m', f)\<in>\<M>'. \<exists>m. (m, f) \<in> \<M> \<and> model_isomorphism \<V> UNIV UNIV m m' f isomorphism"
    using equiv.model_set_isomorphism_axioms
    unfolding model_set_isomorphism_def
    by blast
  with valid_game have
    "\<exists> m. (m, f) \<in> \<M> \<and> model_isomorphism \<V> UNIV UNIV m (V, vf) f isomorphism"
    by blast
  then obtain m :: "('v \<Rightarrow> bool) \<Rightarrow> bool" where
    valid_rule: "(m, f) \<in> \<M>" and iso: "model_isomorphism \<V> UNIV UNIV m (V, vf) f isomorphism"
    by blast
  hence np': "\<not> has_swing_vote AN m v"
    using valid_rule valid_game voter iso np equiv.equiv_swings
    by blast
  have "\<delta>' (V, vf) v = \<delta> m v"
    using valid_rule valid_game voter iso equiv.coincide
    by fastforce (* TODO don't use ff *)
  also have "\<delta> m v = 0"
    using valid_rule voter np' np_ax
    by blast
  finally show "\<delta>' (V, vf) v = 0"
    by simp
next
  fix
    r :: "('v \<Rightarrow> bool) \<Rightarrow> bool" and
    f :: "('v \<Rightarrow> bool) \<Rightarrow> bool" and
    v :: 'v
  assume
    valid_rule: "(r, f) \<in> \<M>" and
    voter: "v \<in> \<V>" and
    np: "\<not> has_swing_vote AN r v" and
    np_ax: "\<forall>(m, f)\<in>\<M>'. \<forall>v\<in>\<V>. \<not> has_swing_vote AN' m v \<longrightarrow> \<delta>' m v = 0"
  show "\<delta> r v = 0"
    sorry
qed

end