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

fun export::"transBdd \<Rightarrow> transaction list" where
  "export [] = []" |
  "export ((tid, state) # bdd) = (
    case state of
      Validated price \<Rightarrow> (tid, price) # export bdd |
      _ \<Rightarrow> export bdd
  )"

(* ----- Exportation en Scala (Isabelle 2018) -------*)

(* Directive d'exportation *)
export_code export traiterMessage in Scala



end

