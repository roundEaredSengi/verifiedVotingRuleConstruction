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

end