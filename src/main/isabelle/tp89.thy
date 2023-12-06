theory tp89
imports Main table "~~/src/HOL/Library/Code_Target_Nat" (* pour l'export Scala *)
begin

(* (client, dealer, transactionNumber) *)
type_synonym transid= "nat*nat*nat"

type_synonym price= "nat" (* "nat*nat" for float ? *)
type_synonym sellerPrice= "price"
type_synonym buyerPrice= "price"

type_synonym potentialSellerPrice= "sellerPrice option"
type_synonym potentialBuyerPrice= "buyerPrice option"

datatype message= 
  Pay transid buyerPrice  
| Ack transid sellerPrice
| Cancel transid

(*
  InProgress (potential seller's price) (potential buyer's price) |
  Validated (agreed price) |
  Canceled
*)
datatype state=
  InProgress potentialSellerPrice potentialBuyerPrice
| Validated price
| Canceled

type_synonym ligneBdd= "state"

(* Le type d'un element de la Bdd: l'identifiant de transaction associée à une ligne de la Bdd *)
type_synonym transBdd= "(transid , ligneBdd) table"

(*
  Le type des transactions validées.
  - transid: transaction's id
  - nat: transaction's total
*)
type_synonym transaction= "transid * price"

(*
  treatPay is only effective for a InProgress transaction and not initialized tid.

  - case \<degree>1: There were no transaction for the tid yet;
  - case \<degree>2: `InProgress None None` should never happen in our implementation but just in case;
  - case \<degree>3: The buyer has set the price, but not the seller. We update the buyerPrice if necessary;
  - case \<degree>4: The buyer has not yet set the price, but the seller has.
      if newPrice and sellerPrice are = 0, it can create a `InProgress Some 0 Some 0`
      but no softlock, as the buyer can set a higher price to validate it;
  - case \<degree>5: The buyer and seller has already set their price.
      We don't need to verify if newPrice > 0 to validate or not,
      because newPrice > oldBuyerPrice::nat so even if oldBuyerPrice = 0, newPrice won't be null;
  - case \<degree>6: The transaction has been locally canceled or validated.
*)
fun treatPay::"transid \<Rightarrow> price \<Rightarrow> transBdd \<Rightarrow> transBdd" where
  "treatPay tid newPrice tbdd = (
    case assoc tid tbdd of
        None \<Rightarrow> modify tid (InProgress None (Some newPrice)) tbdd

      | Some (InProgress None None) \<Rightarrow> modify tid (InProgress None (Some newPrice)) tbdd
      | Some (InProgress None (Some oldBuyerPrice)) \<Rightarrow>
          if newPrice > oldBuyerPrice then
            modify tid (InProgress None (Some newPrice)) tbdd
          else tbdd
      | Some (InProgress (Some sellerPrice) None) \<Rightarrow>
          if newPrice \<ge> sellerPrice \<and> newPrice > 0 then
            modify tid (Validated newPrice) tbdd
          else
            modify tid (InProgress (Some sellerPrice) (Some newPrice)) tbdd
      | Some (InProgress (Some sellerPrice) (Some oldBuyerPrice)) \<Rightarrow>
          if newPrice > oldBuyerPrice then
            if newPrice \<ge> sellerPrice then
              modify tid (Validated newPrice) tbdd
            else
              modify tid (InProgress (Some sellerPrice) (Some newPrice)) tbdd
          else tbdd

      | Some _ \<Rightarrow> tbdd
  )"

(*
  treatAck

  - case \<degree>1: There were no transaction for the tid yet;
  - case \<degree>2: Just for security as our implementation can't create a InProgress None None;
  - case \<degree>3: The seller has set the price, but not the buyer. We update the sellerPrice if necessary;
  - case \<degree>4: The seller has not yet set the price, but the buyer has.
      If newPrice and buyerPrice are = 0 then it will create a ligneBdd:
        (tid, InProgress Some 0 Some 0)
      This is not a softlock of the transaction, as the buyer can set a higher price to validate it;
  - case \<degree>5: The seller and buyer has already set their price.
      Same situation as case\<degree>4 if oldSellerPrice > 0, no softlock;
  - case \<degree>6: The transaction has been locally canceled or validated.
*)
fun treatAck::"transid \<Rightarrow> price \<Rightarrow> transBdd \<Rightarrow> transBdd" where
  "treatAck tid newPrice tbdd = (
    case assoc tid tbdd of
        None \<Rightarrow> modify tid (InProgress (Some newPrice) None) tbdd

      | Some (InProgress None None) \<Rightarrow> modify tid (InProgress (Some newPrice) None) tbdd
      | Some (InProgress (Some oldSellerPrice) None) \<Rightarrow>
          if newPrice < oldSellerPrice then
              modify tid (InProgress (Some newPrice) None) tbdd
          else tbdd
      | Some (InProgress None (Some buyerPrice)) \<Rightarrow>
          if newPrice \<le> buyerPrice \<and> buyerPrice > 0 then
            modify tid (Validated buyerPrice) tbdd
          else
            modify tid (InProgress (Some newPrice) (Some buyerPrice)) tbdd         
      | Some (InProgress (Some oldSellerPrice) (Some buyerPrice)) \<Rightarrow>
          if newPrice < oldSellerPrice then
            if newPrice \<le> buyerPrice \<and> buyerPrice > 0 then
              modify tid (Validated buyerPrice) tbdd
            else
              modify tid (InProgress (Some newPrice) (Some buyerPrice)) tbdd
          else tbdd

      | Some _ \<Rightarrow> tbdd
  )"

fun traiterMessage::"message \<Rightarrow> transBdd \<Rightarrow> transBdd" where
  "traiterMessage (Cancel tid) tbdd = modify tid Canceled tbdd" |
  "traiterMessage (Pay tid price) tbdd = treatPay tid price tbdd" |
  "traiterMessage (Ack tid price) tbdd = treatAck tid price tbdd"

fun traiterMessageList:: "message list \<Rightarrow> transBdd"
where
"traiterMessageList [] = []" |
"traiterMessageList (m#r)= (traiterMessage m (traiterMessageList r))"

fun keyPresent::"'a \<Rightarrow> ('a * 'b) list \<Rightarrow> bool" where
  "keyPresent _ [] = False" |
  "keyPresent e ((key, _) # rem) = (e = key \<or> keyPresent e rem)"

fun export::"transBdd \<Rightarrow> transaction list" where
  "export [] = []" |
  "export ((tid, state) # bdd) = (
    let validated_transactions = export bdd in
    case state of
        Validated price \<Rightarrow> 
          if price = 0 \<or> keyPresent tid validated_transactions then
            validated_transactions
          else
            (tid, price) # validated_transactions
      | _ \<Rightarrow> export bdd
  )"

(* ---- Prop 1: Toutes les transactions validées ont un montant strictement supérieur à 0. *)

lemma totalPositive: "List.member (export tbdd) transaction \<longrightarrow> (snd transaction) > 0"
  sorry

(* ---- Prop2: 
   Dans la liste de transactions validées, tout triplet {\tt (c,m,i)} (où
  {\tt c} est un numéro de client, {\tt m} est un numéro de marchand et {\tt i}
  un numéro de transaction) n'apparaît qu'une seule fois.
*)

lemma transidUnique:
  "List.member (export tbdd) trans1 \<and> List.member (export tbdd) trans2 \<longrightarrow>
      fst trans1 = fst trans2 \<longrightarrow> trans1 = trans2"
  sorry

(* Prop 3 *)
(* Toute transaction (même validée) peut être annulée. *)
(* Prop 4*)
(* Toute transaction annulée l'est définitivement: un message {\tt (Cancel
    (c,m,i))} rend impossible  la validation d'une transaction de numéro {\tt
    i} entre un marchand {\tt m} et un client {\tt c}.*)

(* = Our implementation respects the consent *)
lemma prop3and4: "
  \<not>List.member
    (export (traiterMessage (Cancel tid) (traiterMessageList messages)))
    (tid, anyPrice)
"
  sorry

(* Prop 5:
Si un message {\tt Pay} et un message {\tt Ack}, tels que le montant
  proposé par le {\tt Pay} est strictement supérieur à 0, supérieur ou égal au
  montant proposé par le message {\tt Ack} et non annulée, ont été envoyés alors la transaction figure
  dans la liste des transactions validées.
*)

lemma prop5: "
  \<not>List.member messages (Cancel tid) \<and>
  List.member messages (Pay tid buyerPrice) \<and>
  List.member messages (Ack tid sellerPrice) \<and>
  buyerPrice > 0 \<and> buyerPrice \<ge> sellerPrice \<longrightarrow>
    List.member (export (traiterMessageList messages)) (tid, buyerPrice)
"
  sorry

(* Prop 6:
Toute transaction figurant dans la liste des transactions validées l'a été
  par un message {\tt Pay} et un message {\tt Ack} tels que le montant proposé
  par le {\tt Pay} est supérieur ou égal au montant proposé par le message {\tt
    Ack}.  *)

lemma prop6: "
  List.member (export (traiterMessageList messages)) (tid, buyerPrice) \<longrightarrow> 
    (\<exists> sellerPrice::nat.  
      List.member messages (Pay tid buyerPrice) \<and>
      List.member messages (Ack tid sellerPrice) \<and>
      buyerPrice > 0 \<and> buyerPrice \<ge> sellerPrice
    )
"
  sorry

(* Prop 7 *)
(*
  Si un client (resp. marchand) a proposé un montant {\tt am} pour une
  transaction, tout montant {\tt am'} inférieur (resp. supérieur) proposé par la 
  suite est ignoré par l'agent de validation.
*)

lemma prop7customer: "
  buyerPrice > lowerBuyerPrice \<and>
  List.member earlyMessages (Pay tid buyerPrice) \<and>
  List.member lateMessages (Pay tid lowerBuyerPrice) \<longrightarrow>
    List.member (export (traiterMessageList (lateMessage@earlyMessages))) (tid, agreedPrice) \<longrightarrow>
      agreedPrice = buyerPrice
"
  sorry

(* TODO: prop7dealer *)
lemma prop7dealer: "
  sellerPrice < higherSellerPrice \<and>
  List.member earlyMessages (Ack tid sellerPrice) \<and>
  List.member lateMessages (Ack tid higherSellerPrice) \<longrightarrow>
    List.member (export (traiterMessageList (lateMessage@earlyMessages))) (tid, agreedPrice) \<longrightarrow>
      agreedPrice \<ge> sellerPrice
"
  oops

lemma prop7: "prop7customer \<and> prop7dealer"
  oops

(* Prop 8 *)
(* Toute transaction validée ne peut être renégociée: si une transaction a
  été validée avec un montant {\tt am} celui-ci ne peut être changé.
*)

lemma prop8: "
  List.member (traiterMessageList messages) (tid, Validated agreedPrice) \<and>
  \<not>List.member lastMessages (Cancel tid) \<longrightarrow>
    List.member (export (traiterMessageList (lastMessages @ messages))) (tid, agreedPrice)
"
  sorry

(* Prop9: Le montant associé à une transaction validée correspond à un prix proposé
  par le client pour cette transaction. *)
    
lemma prop9: "
  List.member (export (traiterMessageList messages)) (tid, agreedPrice) \<longrightarrow>
    List.member messages (Pay tid agreedPrice)
"
  sorry

(* ----- Exportation en Scala (Isabelle 2018) -------*)

(* Directive d'exportation *)
export_code export traiterMessage in Scala



end

