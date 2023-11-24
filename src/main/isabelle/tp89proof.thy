theory tp89proof
imports Main table "~~/src/HOL/Library/Code_Target_Nat" 
begin

(* quickcheck [size=7,tester=narrowing,timeout=300]
   nitpick [timeout=300]

  Si on veut du temps supplémentaire avec sledgehammer:
  sledgehammer [provers=e cvc4 spass remote_vampire z3,timeout=300]

  Pour guider l'utilisation de théorèmes particuliers: 
  sledgehammer [provers=e cvc4 spass remote_vampire z3,timeout=300] (add: th1 th2 ...)

*)


(* 
  Très important!
  ---------------

  Il faut vous assurer en même temps que vous développez votre code et vos preuves
  que le 'export_code' réussi.

  En particulier, à partir du moment où on utilise "~~/src/HOL/Library/Code_Target_Nat" pour 
  exporter les nat vers des nat Scala, on perd la possibilité de faire du pattern matching 
  sur ces nat. Par exemple une fonction avec des équations de la forme:

  f 0 = ...
  f (Suc x) = ...

 Ne sera plus exportable. Ca ne sert donc à rien de tenter de la prouver, car vous ne pourrez 
 pas l'exporter telle quelle.
*)

type_synonym transid= "nat*nat*nat"

datatype message= 
  Pay transid nat  
| Ack transid nat
| Cancel transid

type_synonym ligneBdd= ""

(* Le type d'un element de la Bdd: l'identifiant de transaction associée à une ligne de la Bdd *)

type_synonym transBdd= "(transid , ligneBdd) table"

(* Le type des transactions validées *)
type_synonym transaction= "transid * nat"

(* Il est conseillé de séparer le traitement des messages en 3 sous-fonctions: 
  traiterPay, traiterAck et traiterCancel *)


(* Lemmes intermédiaires conseillés *)

(* Lemme 1*)
(* Soit m un message d'identifiant tid2. Si tid\<noteq>tid2 alors la valeur associée à tid dans la
   base de donnée ne sera pas modifiée par le traitement du message m.

   Au préalable, il est conseillé de faire des lemmes intermédiaires pour les 3 types de messages à traiter: Pay, Ack, Cancel et
   de les utiliser pour prouver celui-ci *)


(* Lemme 2 *)
(* Quelque soit la bdd quand on traite un message (Cancel tid), on obtient une nouvelle 
   bdd dans laquelle tid est associé à un statut annulé, et des prix client et marchand 
   indéfinis *)
 
(* On traite les messages en commencant par la fin de la liste. On voit la liste comme une file. 
   Coherent avec ce qui se passe dans l'IHM. Cela simplifie grandement les preuves! *)

fun traiterMessageList:: "message list \<Rightarrow> transBdd"
where
"traiterMessageList [] = []" |
"traiterMessageList (m#r)= (traiterMessage m (traiterMessageList r))"


(* Définir une fonction validOne déterminant si une ligne de la Bdd est valide.
   Une bdd tbdd sera valide si (forAll validOne tbdd) est vraie *)

(* Lemme 3 *)
(* Si une bdd est valide, alors quelque soit la ligne obtenue par la fonction assoc, celle-ci est valide *)

(* Lemme 4 *)
(* Si une bdd est valide, pour toute ligne associée à un tid, si le statut est Validated, 
   cela signifie que le prix marchand est supérieur ou égal au prix client *)

(* Lemme 5 *)
(* Si une bdd est valide, elle restera valide pour toutes les modifications (valides) opérées. *)
(* Par exemple:
  Si une bdd est valide et que l'on modifie la ligne associée à tid par une nouvelle ligne 
  correcte alors la nouvelle bdd est valide également.

  Définir et prouver tous les cas possibles de modification dans des lemmes distincts.
*)

(* Lemme 6 *)
(* Si une bdd est valide alors pour toute ligne associée à tid, si le statut est Validated alors p1 et p2 ne peuvent être indéfinis *)

(* Lemme 7 *)
(* Dans une bdd valide alors pour toute ligne associée à tid, avec des prix client et marchand définis, si le prix client est supérieur
   ou égal au prix du marchand alors le statut de la ligne est Validated *)

(* Lemme 8 *)
(* Dans une bdd valide, pour toute ligne associée à tid, si le statut est Partial, alors le prix du client ou du marchand est défini. *)

(* Lemme 9 *)
(* Si une bdd est valide, traiter un message Pay sur cette bdd rendra une bdd valide *)

(* Lemme 10 *)
(* Si une bdd est valide, traiter un message Ack sur cette bdd rendra une bdd valide *)

(* Lemme 11 *)
(* Si une bdd est valide, traiter un message Cancel sur cette bdd rendra une bdd valide *)

(* Lemme 12 *)
(* Si une bdd est valide, traiter tout message sur cette bdd rendra une bdd valide *)

(* Lemme 13 *)
(* traiterMessageList ne construit que des bdds valides *)


(* ---- Prop 1: Toutes les transactions validées ont un montant strictement supérieur à 0. *)

(* Lemme intermédiaire: Lemme 14 *)
(* A partir de toute bdd valide, export contruit une liste de couples (tid,p) tel que
   p est strictement positif *)

(* Définir Prop1 *)


(* ---- Prop2: 
   Dans la liste de transactions validées, tout triplet {\tt (c,m,i)} (où
  {\tt c} est un numéro de client, {\tt m} est un numéro de marchand et {\tt i}
  un numéro de transaction) n'apparaît qu'une seule fois.
*)

(* Lemmes intermédiaires *)

(* Lemme 15 *)
(* Si une bdd a des clés uniques, traiter un message Pay rend une bdd avec des clés uniques *)

(* Lemme 16 *)
(* Si une bdd a des clés uniques, traiter un message Ack rend une bdd avec des clés uniques *)

(* Lemme 17 *)
(* Si une bdd a des clés uniques, traiter un message Pay/Ack/Cancel rend une bdd avec des clés uniques *)

(* Lemme 18 *)
(* traiterMessageList rend une bdd avec des clés uniques *)

(* Lemme 19 *)
(* Les transactions ne figurant pas dans la bdd, ne figurent pas dans l'export *)

(* Lemme 20 *)
(* Si les clés sont unique dans une bdd, elles le seront dans l'export *)

(* Définir prop2 *)


(* Prop 3 *)
(* Toute transaction (même validée) peut être annulée. *)
(* Prop 4*)
(* Toute transaction annulée l'est définitivement: un message {\tt (Cancel
    (c,m,i))} rend impossible  la validation d'une transaction de numéro {\tt
    i} entre un marchand {\tt m} et un client {\tt c}.*)

(* On fait les deux en une seule propriété *)

(* Lemme 21 *)
(* Dans une bdd si le statut d'une transaction est Cancelled, celui-ci reste Cancelled quelque soit le message traité *)

(* Lemme 22 *)
(* Si un message (Cancel tid) apparaît dans une liste de message et que l'on construit
   une bdd par traitement de toute cette liste de message, alors dans cette bdd, la ligne 
   associée à la transation tid aura un statut Cancelled et les prix seront indéfinis *)

(* Lemme 23 *)
(* Dans une bdd si une transaction est annulée, celle-ci n'apparaîtra pas dans l'export *)

(* Définir prop 3 et 4 *)


(* Prop 5:
Si un message {\tt Pay} et un message {\tt Ack}, tels que le montant
  proposé par le {\tt Pay} est strictement supérieur à 0, supérieur ou égal au
  montant proposé par le message {\tt Ack} et non annulée, ont été envoyés alors la transaction figure
  dans la liste des transactions validées.
*)

(* Lemme 24 *)
(* Si les clés sont uniques dans une bdd, une transition aura le statut Validated si et seulement si 
   elle figure dans l'export *)

(* Lemme 25 *)
(* Si le message (Cancel tid) n'apparaît PAS dans une liste de message et que l'on construit
   une bdd par traitement de toute cette liste de message, la ligne 
   associée à la transation tid dans la bdd ne pourra avoir le statut Cancelled *)

(* Lemme 26 *)
(* Si une liste de message lmess contient un message de la forme (Pay tid mc) et ne contient pas de (Cancel tid) alors 
   alors il existe une ligne associée à tid dans la bdd obtenue par traitement de lmess et le prix client est défini. *)

(* Lemme 27 *)
(* Si une liste de message lmess contient un message de la forme (Ack tid mc) et ne contient pas de (Cancel tid) alors 
   alors il existe une ligne associée à tid dans la bdd obtenue par traitement de lmess et le prix marchand est défini. *)


(* Lemme 28 *)
lemma PricePayMessage: "(mc > 0 \<and>
  (forAll validOne tbdd) \<and> ((assoc tid tbdd) = (Some (p3,p4,s2))) \<and> s2\<noteq>Validated 
    \<and> ((assoc tid (traiterMessage (Pay tid mc) tbdd)) = (Some ((Mynat p1),p2,s))))
      \<longrightarrow> p1\<ge>mc"
sorry

(* Lemme 29 *)
lemma PricePayMessage2: "(mc > 0 \<and>
  (forAll validOne tbdd) \<and> ((assoc tid (traiterMessage (Pay tid mc) tbdd)) = (Some ((Mynat p1),p2,s))) 
  \<and> s\<noteq>Validated) \<longrightarrow> p1\<ge>mc"
sorry

(* Lemme 30 *)
(* Un message Ack ne peut changer le prix client dans une base valide *)

(* Lemme 31 *)
(* Un message Pay ne peut changer le prix marchand dans une base valide*)

(* Lemme 31 bis *)
(* Soit une tbdd valide, si dans cette base le prix client est mc pour un tid donné, alors
   Traiter un message Pay sur le même tid avec un prix inférieur ou égal à mc, ne change
   pas la base de données *)

(* Lemme 32 *)
(* Soit une bdd obtenue par traitement d'une liste de message contenant un message (Pay tid mc)
   Si cette bdd contient une ligne pour tid, que le prix client est défini et vaut p1, alors p1 est supérieur
   ou égal à mc. 
 *)

(* Lemme 33 *)
lemma PriceAckMessage: "((forAll validOne tbdd) \<and> ((assoc tid tbdd) = (Some (p3,p4,s2))) \<and> s2\<noteq>Validated 
    \<and> ((assoc tid (traiterMessage (Ack tid mm) tbdd)) = (Some (p1,(Mynat p2),s))))
      \<longrightarrow> p2\<le>mm"
sorry

(* Lemme 34 *)
lemma PriceAckMessage2: "((forAll validOne tbdd) \<and> ((assoc tid (traiterMessage (Ack tid mm) tbdd)) = (Some (p1,(Mynat p2),s))) \<and> s\<noteq>Validated)
  \<longrightarrow> p2\<le>mm"
sorry


(* Lemme 35 *)
(* Soit une bdd obtenue par traitement d'une liste de message contenant un message (Ack tid mm)
   Si cette bdd contient une ligne pour tid, que le prix marchand est défini et vaut p2, alors p2 est inférieur
   ou égal à mm. 
 *)

(* Lemme 36 *)
(* Si une liste de message lmess contient un (Pay tid mc) et (Ack tid mm) avec mc supérieur ou égal 
   à mm (et mc supérieur à 0) et pas de (Cancel tid) alors il existe une ligne associée 
   à tid dans la bdd générée en traitant lmess. Dans cette ligne le statut est Validated et les prix 
   client et marchand sont définis. *)


(* Définir Prop5 *)


(* Prop 6:
Toute transaction figurant dans la liste des transactions validées l'a été
  par un message {\tt Pay} et un message {\tt Ack} tels que le montant proposé
  par le {\tt Pay} est supérieur ou égal au montant proposé par le message {\tt
    Ack}.  *)

(* Lemme 37 *)
(*Soit une bdd produite par traitement d'une liste de messages lmess. 
  Dans la bdd tout prix client mc associé à tid, vient d'un message (Pay tid mc) figurant dans lmess *)

(* Lemme 38 *)
(*Soit une bdd produite par traitement d'une liste de messages lmess. 
  Dans la bdd tout prix marchand mm associé à tid, vient d'un message (Ack tid mm) figurant dans lmess *)

(* Lemme 39 *)
(* Si une transaction figure dans le export alors elle a une ligne dans la bdd avec un statut Validated *)

(* Définir Prop6 *)


(* Prop 7 *)
(*
  Si un client (resp. marchand) a proposé un montant {\tt am} pour une
  transaction, tout montant {\tt am'} inférieur (resp. supérieur) proposé par la 
  suite est ignoré par l'agent de validation.
*)

(* Lemme 40 *)
(* Dans une bdd si une transaction est validée, elle le reste quelque soit le message de type Pay que l'on traite et ses
   valeurs de prix marchand et client sont conservées. *)

(* Lemme 41 *)
(* Dans une bdd si une transaction est validée, elle le reste quelque soit le message de type Ack que l'on traite et ses
   valeurs de prix marchand et client sont conservées. *)


(* Prop7 pour un message client *)
(* Soit tbdd une bdd obtenue après traitement d'une liste de messages lmess et mc1 et mc2 deux prix tels que mc1>0 et mc2>mc1.
   Soit lmess une liste de messages contenant (Pay tid mc2) et ne contenant pas (Pay tid mc1). Si l'on traite (Pay tid mc1) 
   sur tbdd, ça ne changera pas la ligne associée à tid dans la bdd *)

(* Prop7 pour un message marchand *)
(* Soit tbdd une bdd obtenue après traitement d'une liste de messages lmess et mm1 et mm2 deux prix tels que mm2<mm1.
   Soit lmess une liste de messages contenant (Pay tid mm2) et ne contenant pas (Pay tid mm1). Si l'on traite (Pay tid mm1) 
   sur tbdd, ça ne changera pas la ligne associée à tid dans la bdd *)

(* Prop 8 *)

(* Toute transaction validée ne peut être renégociée: si une transaction a
  été validée avec un montant {\tt am} celui-ci ne peut être changé.
*)

(* Lemme 42 *)
(* Dans une bdd si la ligne associée à un tid a un statut Validated, quelque soit le message (différent de Cancel) traité
   sur la bdd, les prix et le statut de la ligne ne change pas. *)


(* Définir Prop8 *)


(* Prop9: Le montant associé à une transaction validée correspond à un prix proposé
  par le client pour cette transaction. *)

(* Pas de lemmes intermédiaires *)


end

