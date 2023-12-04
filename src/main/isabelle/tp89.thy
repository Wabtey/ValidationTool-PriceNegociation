theory tp89
imports Main "~~/src/HOL/Library/Code_Target_Nat" (* pour l'export Scala *)
begin

(* 
quickcheck_params [size=6,tester=narrowing,timeout=120]
nitpick_params [timeout=120]
*)

(* (client, dealer, transactionNumber) *)
type_synonym transid= "nat*nat*nat"

type_synonym price= "nat" (* "nat*nat" for float ? *)
type_synonym sellerPrice= "price"
type_synonym buyerPrice= "price"

datatype message= 
  Pay transid buyerPrice  
| Ack transid sellerPrice
| Cancel transid

(*
  InProgress (seller's price) (buyer's price) |
  Validated (agreed price) |
  Canceled
*)
datatype state=
  InProgress sellerPrice buyerPrice
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

(* Il est conseillé de séparer le traitement des messages en 3 sous-fonctions: 
  traiterPay, traiterAck et traiterCancel *)

(* treatPay is only effective for a inprogress transaction *)
fun treatPay::"transid \<Rightarrow> price \<Rightarrow> transBdd \<Rightarrow> transBdd" where
  "treatPay tid newPrice tbdd = (
    case assoc tid tbdd of
        Some (InProgress sellerPrice oldBuyerPrice) \<Rightarrow> 
          if (newPrice > oldBuyerPrice) then
            modify tid (InProgress sellerPrice newPrice) tbdd
          else tbdd
      | _ \<Rightarrow> tbdd
  )"

fun treatAck::"transid \<Rightarrow> price \<Rightarrow> transBdd \<Rightarrow> transBdd" where
  "treatAck tid newPrice tbdd = (
    case assoc tid tbdd of
        Some (InProgress oldSellerPrice buyerPrice) \<Rightarrow>
          if (newPrice < oldSellerPrice) then
            modify tid (InProgress newPrice buyerPrice) tbdd
          else tbdd
      | _ \<Rightarrow> tbdd
  )"

fun traiterMessage::"message \<Rightarrow> transBdd \<Rightarrow> transBdd" where
  (* modify only changes existing data (ignores if not in the table) *)
  "traiterMessage (Cancel tid) tbdd = modify tid Canceled tbdd" |
  "traiterMessage (Pay tid price) tbdd = treatPay tid price tbdd" |
  "traiterMessage (Ack tid price) tbdd = treatAck tid price tbdd"

fun export::"transBdd \<Rightarrow> transction list" where
  "export tbdd = []"

fun traiterMessageList:: "message list \<Rightarrow> transBdd"
where
"traiterMessageList [] = []" |
"traiterMessageList (m#r)= (traiterMessage m (traiterMessageList r))"

(* ----- Exportation en Scala (Isabelle 2018) -------*)

(* Directive d'exportation *)
export_code export traiterMessage in Scala



end

