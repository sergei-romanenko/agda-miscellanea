theory Synapse
imports Main
begin

inductive synapse :: "(nat * nat * nat) => bool" where
  "synapse (i, 0, 0)" |
  "synapse (Suc i, d, v) ==> synapse (i + d, 0, Suc v)" |
  "synapse (i, d, Suc v) ==> synapse (i + d + v, (Suc 0), 0)" |
  "synapse (Suc i, d, v) ==> synapse (i + d + v, (Suc 0), 0)"

fun unsafe :: "(nat * nat * nat) => bool" where 
  "unsafe (x, Suc y, Suc z) = True" |
  "unsafe (x, Suc (Suc y), z) = True" |
  "unsafe (x, y, z) = False" 


inductive synapse' :: "(nat * nat * nat) => bool" where
  "synapse'(_, Suc 0, 0)" |
  "synapse'(_, 0, _)"

lemma inclusion: "synapse c ==> synapse' c"
  apply(erule synapse.induct)
  apply(erule synapse'.cases | simp add: synapse'.intros)+
done

lemma safety: "synapse' c ==> ~unsafe c"
  apply(erule synapse'.cases)
  apply(auto)
done

theorem valid:
  assumes A: "synapse c" shows "~unsafe c"
  using A inclusion safety by (auto)

end
