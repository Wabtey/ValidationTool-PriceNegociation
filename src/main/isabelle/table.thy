theory table
imports Main
begin

(* Le type des tables d'associations (maps) *)
type_synonym ('a,'b) table= "('a * 'b) list"

datatype 'a option= Some 'a | None

(* Pour une clé k et une table t, (assoc k t) rend None si la clé k ne figure pas
   dans t et (Some v) si k est associée à v dans t *)
fun assoc:: "'a \<Rightarrow> ('a ,'b) table \<Rightarrow> 'b option"
where
"assoc _ [] = None" |
"assoc x1 ((x,y)#xs)= (if x=x1 then Some(y) else (assoc x1 xs))"

(* Pour une clé k, une valeur v et une table t, (modify k v t) rend la table dans laquelle
   k est associée à v. Si l'association n'existait pas elle est crée. *)
fun modify:: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) table \<Rightarrow> ('a, 'b) table"
where
"modify x y [] = [(x,y)]" |
"modify x y ((z,u)#r) = (if x=z then (x,y)#r else ((z,u)#(modify x y r)))"

(* Toutes les clés sont uniques dans la table t *)
fun uniqueKey::"('a,'b) table \<Rightarrow> bool"
where
"uniqueKey [] = True" |
"uniqueKey ((x,_)#r) = ((assoc x r) = None \<and> uniqueKey r)"


(* Lemme1: Si toutes les clés sont uniques dans la table t, un couple (k,v) appartient à la liste t
   si et seulement quand on cherche k dans la table on trouve v. *)

(* Lemme2: Soit une table t, si on modifie la valeur associée à k dans t (on lui associe une nouvelle valeur v), 
   alors si l'on cherche k dans t on obtient v. *)

(* Lemme3: Soit une table t, dans laquelle k2 n'apparait pas.
   Si on change la valeur associée à k (k\<noteq>k2) dans t, alors si l'on 
   cherche k2 dans t, elle n'apparait toujours pas. *)

(* Lemme4: Soit une table t, dans laquelle k est associée à la valeur v.
   Si on change la valeur associée à k2 (k\<noteq>k2) dans t, alors si l'on cherche k 
   dans t, elle est toujours associée à v. *) 

(* Lemme5: Si toutes les clés sont uniques dans la table t, ça sera le cas dans la table t dans laquelle
   on applique une modification quelconque *)

(* pour tout prédicat p et toute liste l, (forAll p l) si tous les éléments de l satisfont p *)
fun forAll:: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
where 
"forAll _ [] = True" |
"forAll p (x#r) = ((p x) \<and> (forAll p r))"

(* Lemme6: Si tous les éléments d'une liste l satisfont un prédicat p, et que e appartient 
   à la liste p, alors e satisfait p. *)

end
