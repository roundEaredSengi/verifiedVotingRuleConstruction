section \<open>Cooperative and Simple Games\<close>

theory Cooperative_Game
  imports HOL.Real

begin

subsection \<open>Definition\<close>

type_synonym 'v Cooperative_Game = "'v set \<times> ('v \<Rightarrow> real)"

fun players :: "'v Cooperative_Game \<Rightarrow> 'v set" where
  "players G = fst G"

fun payoff :: "'v Cooperative_Game \<Rightarrow> ('v \<Rightarrow> real)" where
  "payoff G = snd G"

fun restricted_game :: "'v set \<Rightarrow> 'v Cooperative_Game \<Rightarrow> 'v Cooperative_Game" where
  "restricted_game V G = (V, payoff G)" 

fun total_payoff :: "'v Cooperative_Game \<Rightarrow> real" where
  "total_payoff G = (\<Sum> v :: 'v \<in> players G. payoff G v)"

fun partial_payoff :: "'v Cooperative_Game \<Rightarrow>'v set \<Rightarrow> real" where
  "partial_payoff G X = total_payoff (restricted_game X G)"

fun monotone :: "'v Cooperative_Game \<Rightarrow> bool" where
  "monotone G = (\<forall> S T. (S \<subseteq> T \<and> T \<subseteq> players G) \<longrightarrow> 
    partial_payoff G S \<le> partial_payoff G T)"

fun null :: "'v Cooperative_Game \<Rightarrow> bool" where
  "null G = (partial_payoff G {} = 0)"

fun proper :: "'v Cooperative_Game \<Rightarrow> bool" where
  "proper G = (partial_payoff G (players G) > 0)" 

fun simple_voting_game :: "'v Cooperative_Game \<Rightarrow> bool" where
  "simple_voting_game G = 
      (total_payoff G = 1 \<and> monotone G \<and> null G)"

abbreviation num_players :: "'v Cooperative_Game \<Rightarrow> nat" where
  "num_players G \<equiv> card (players G)"

subsection \<open>Classical Power Indices\<close>

fun swing_votes :: "'v Cooperative_Game \<Rightarrow> 'v \<Rightarrow> ('v set) set" where
  "swing_votes G v = 
    {S. S \<subseteq> players G \<and> partial_payoff G (S - {v}) \<noteq> partial_payoff G (S \<union> {v})}"

abbreviation pos_swing_votes :: "'v Cooperative_Game \<Rightarrow> 'v \<Rightarrow> ('v set) set" where
  "pos_swing_votes G v \<equiv> {S. S \<in> swing_votes G v \<and> v \<in> S}"

fun banzhaf :: "'v Cooperative_Game \<Rightarrow> ('v \<Rightarrow> real)" where
  "banzhaf G v = 1/(2^(num_players G)) * (card (swing_votes G v))"

fun shapley_shubik :: "'v Cooperative_Game \<Rightarrow> ('v \<Rightarrow> real)" where
  "shapley_shubik G v = 1/(fact (num_players G)) * 
    (\<Sum> S \<in> pos_swing_votes G v. (fact (card S - 1)) * (fact (card (players G - S))))"

end