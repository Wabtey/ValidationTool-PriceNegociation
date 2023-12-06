package validator.FlorianEpain;

import bank._

// Automatic conversion of bank.message to tp89.messages and Nat to bank.Nat
object Converter {
  implicit def bank2message(m: bank.message): tp89.message =
    m match {
      case bank.Pay(
            (bank.Nat.Nata(c), (bank.Nat.Nata(m), bank.Nat.Nata(i))),
            bank.Nat.Nata(p)
          ) =>
        tp89.Pay((Nat.Nata(c), (Nat.Nata(m), Nat.Nata(i))), Nat.Nata(p))
      case bank.Ack(
            (bank.Nat.Nata(c), (bank.Nat.Nata(m), bank.Nat.Nata(i))),
            bank.Nat.Nata(p)
          ) =>
        tp89.Ack((Nat.Nata(c), (Nat.Nata(m), Nat.Nata(i))), Nat.Nata(p))
      case bank.Cancel(
            (bank.Nat.Nata(c), (bank.Nat.Nata(m), bank.Nat.Nata(i)))
          ) =>
        tp89.Cancel((Nat.Nata(c), (Nat.Nata(m), Nat.Nata(i))))
    }

  implicit def trans2bankTrans(
      l: List[((Nat.nat, (Nat.nat, Nat.nat)), Nat.nat)]
  ): List[((bank.Nat.nat, (bank.Nat.nat, bank.Nat.nat)), bank.Nat.nat)] =
    l match {
      case Nil => Nil
      case ((Nat.Nata(c), (Nat.Nata(m), Nat.Nata(i))), Nat.Nata(p)) :: r =>
        (
          (bank.Nat.Nata(c), (bank.Nat.Nata(m), bank.Nat.Nata(i))),
          bank.Nat.Nata(p)
        ) :: trans2bankTrans(r)
    }
}

import Converter._

/* The object to complete */
class ConcreteValidator extends TransValidator {
  def process(m: message): Unit = {}
  // TODO: getValidTrans()
  def getValidTrans = List()
}
object Product_Type {

  def equal_proda[A: HOL.equal, B: HOL.equal](x0: (A, B), x1: (A, B)): Boolean =
    (x0, x1) match {
      case ((x1, x2), (y1, y2)) => HOL.eq[A](x1, y1) && HOL.eq[B](x2, y2)
    }

} /* object Product_Type */

object table {

  abstract sealed class option[A]
  final case class Somea[A](a: A) extends option[A]
  final case class Nonea[A]() extends option[A]

  def assoc[A: HOL.equal, B](uu: A, x1: List[(A, B)]): option[B] =
    (uu, x1) match {
      case (uu, Nil) => Nonea[B]()
      case (x1, (x, y) :: xs) =>
        (if (HOL.eq[A](x, x1)) Somea[B](y) else assoc[A, B](x1, xs))
    }

  def modify[A: HOL.equal, B](x: A, y: B, xa2: List[(A, B)]): List[(A, B)] =
    (x, y, xa2) match {
      case (x, y, Nil) => List((x, y))
      case (x, y, (z, u) :: r) =>
        (if (HOL.eq[A](x, z)) (x, y) :: r else (z, u) :: modify[A, B](x, y, r))
    }

} /* object table */

object tp89 {

  abstract sealed class state
  final case class InProgress(
      a: table.option[Nat.nat],
      b: table.option[Nat.nat]
  ) extends state
  final case class Validated(a: Nat.nat) extends state
  final case class Canceled() extends state

  abstract sealed class message
  final case class Pay(a: (Nat.nat, (Nat.nat, Nat.nat)), b: Nat.nat)
      extends message
  final case class Ack(a: (Nat.nat, (Nat.nat, Nat.nat)), b: Nat.nat)
      extends message
  final case class Cancel(a: (Nat.nat, (Nat.nat, Nat.nat))) extends message

  def keyPresent[A: HOL.equal, B](uu: A, x1: List[(A, B)]): Boolean =
    (uu, x1) match {
      case (uu, Nil) => false
      case (e, (key, uv) :: rem) =>
        HOL.eq[A](e, key) || keyPresent[A, B](e, rem)
    }

  def export(
      x0: List[((Nat.nat, (Nat.nat, Nat.nat)), state)]
  ): List[((Nat.nat, (Nat.nat, Nat.nat)), Nat.nat)] =
    x0 match {
      case Nil => Nil
      case (tid, state) :: bdd => {
        val validated_transactions
            : List[((Nat.nat, (Nat.nat, Nat.nat)), Nat.nat)] = export(bdd);
        (state match {
          case InProgress(_, _) => export(bdd)
          case Validated(price) =>
            (if (
               Nat.equal_nata(price, Nat.zero_nat) ||
               keyPresent[(Nat.nat, (Nat.nat, Nat.nat)), Nat.nat](
                 tid,
                 validated_transactions
               )
             )
               validated_transactions
             else (tid, price) :: validated_transactions)
          case Canceled() => export(bdd)
        })
      }
    }

  def treatAck(
      tid: (Nat.nat, (Nat.nat, Nat.nat)),
      newPrice: Nat.nat,
      tbdd: List[((Nat.nat, (Nat.nat, Nat.nat)), state)]
  ): List[((Nat.nat, (Nat.nat, Nat.nat)), state)] =
    (table.assoc[(Nat.nat, (Nat.nat, Nat.nat)), state](tid, tbdd) match {
      case table.Somea(
            InProgress(table.Somea(oldSellerPrice), table.Somea(buyerPrice))
          ) => (
        if (Nat.less_nat(newPrice, oldSellerPrice))
          (if (
             Nat.less_eq_nat(newPrice, buyerPrice) &&
             Nat.less_nat(Nat.zero_nat, buyerPrice)
           )
             table.modify[(Nat.nat, (Nat.nat, Nat.nat)), state](
               tid,
               Validated(buyerPrice),
               tbdd
             )
           else
             table.modify[(Nat.nat, (Nat.nat, Nat.nat)), state](
               tid,
               InProgress(
                 table.Somea[Nat.nat](newPrice),
                 table.Somea[Nat.nat](buyerPrice)
               ),
               tbdd
             ))
        else tbdd
      )
      case table.Somea(
            InProgress(table.Somea(oldSellerPrice), table.Nonea())
          ) =>
        (if (Nat.less_nat(newPrice, oldSellerPrice))
           table.modify[(Nat.nat, (Nat.nat, Nat.nat)), state](
             tid,
             InProgress(table.Somea[Nat.nat](newPrice), table.Nonea[Nat.nat]()),
             tbdd
           )
         else tbdd)
      case table.Somea(InProgress(table.Nonea(), table.Somea(buyerPrice))) =>
        (if (
           Nat.less_eq_nat(newPrice, buyerPrice) &&
           Nat.less_nat(Nat.zero_nat, buyerPrice)
         )
           table.modify[(Nat.nat, (Nat.nat, Nat.nat)), state](
             tid,
             Validated(buyerPrice),
             tbdd
           )
         else
           table.modify[(Nat.nat, (Nat.nat, Nat.nat)), state](
             tid,
             InProgress(
               table.Somea[Nat.nat](newPrice),
               table.Somea[Nat.nat](buyerPrice)
             ),
             tbdd
           ))
      case table.Somea(InProgress(table.Nonea(), table.Nonea())) =>
        table.modify[(Nat.nat, (Nat.nat, Nat.nat)), state](
          tid,
          InProgress(table.Somea[Nat.nat](newPrice), table.Nonea[Nat.nat]()),
          tbdd
        )
      case table.Somea(Validated(_)) => tbdd
      case table.Somea(Canceled())   => tbdd
      case table.Nonea() =>
        table.modify[(Nat.nat, (Nat.nat, Nat.nat)), state](
          tid,
          InProgress(table.Somea[Nat.nat](newPrice), table.Nonea[Nat.nat]()),
          tbdd
        )
    })

  def treatPay(
      tid: (Nat.nat, (Nat.nat, Nat.nat)),
      newPrice: Nat.nat,
      tbdd: List[((Nat.nat, (Nat.nat, Nat.nat)), state)]
  ): List[((Nat.nat, (Nat.nat, Nat.nat)), state)] =
    (table.assoc[(Nat.nat, (Nat.nat, Nat.nat)), state](tid, tbdd) match {
      case table.Somea(
            InProgress(table.Somea(sellerPrice), table.Somea(oldBuyerPrice))
          ) => (
        if (Nat.less_nat(oldBuyerPrice, newPrice))
          (if (Nat.less_eq_nat(sellerPrice, newPrice))
             table.modify[(Nat.nat, (Nat.nat, Nat.nat)), state](
               tid,
               Validated(newPrice),
               tbdd
             )
           else
             table.modify[(Nat.nat, (Nat.nat, Nat.nat)), state](
               tid,
               InProgress(
                 table.Somea[Nat.nat](sellerPrice),
                 table.Somea[Nat.nat](newPrice)
               ),
               tbdd
             ))
        else tbdd
      )
      case table.Somea(InProgress(table.Somea(sellerPrice), table.Nonea())) =>
        (if (
           Nat.less_eq_nat(sellerPrice, newPrice) &&
           Nat.less_nat(Nat.zero_nat, newPrice)
         )
           table.modify[(Nat.nat, (Nat.nat, Nat.nat)), state](
             tid,
             Validated(newPrice),
             tbdd
           )
         else
           table.modify[(Nat.nat, (Nat.nat, Nat.nat)), state](
             tid,
             InProgress(
               table.Somea[Nat.nat](sellerPrice),
               table.Somea[Nat.nat](newPrice)
             ),
             tbdd
           ))
      case table.Somea(InProgress(table.Nonea(), table.Somea(oldBuyerPrice))) =>
        (if (Nat.less_nat(oldBuyerPrice, newPrice))
           table.modify[(Nat.nat, (Nat.nat, Nat.nat)), state](
             tid,
             InProgress(table.Nonea[Nat.nat](), table.Somea[Nat.nat](newPrice)),
             tbdd
           )
         else tbdd)
      case table.Somea(InProgress(table.Nonea(), table.Nonea())) =>
        table.modify[(Nat.nat, (Nat.nat, Nat.nat)), state](
          tid,
          InProgress(table.Nonea[Nat.nat](), table.Somea[Nat.nat](newPrice)),
          tbdd
        )
      case table.Somea(Validated(_)) => tbdd
      case table.Somea(Canceled())   => tbdd
      case table.Nonea() =>
        table.modify[(Nat.nat, (Nat.nat, Nat.nat)), state](
          tid,
          InProgress(table.Nonea[Nat.nat](), table.Somea[Nat.nat](newPrice)),
          tbdd
        )
    })

  def traiterMessage(
      x0: message,
      tbdd: List[((Nat.nat, (Nat.nat, Nat.nat)), state)]
  ): List[((Nat.nat, (Nat.nat, Nat.nat)), state)] =
    (x0, tbdd) match {
      case (Cancel(tid), tbdd) =>
        table
          .modify[(Nat.nat, (Nat.nat, Nat.nat)), state](tid, Canceled(), tbdd)
      case (Pay(tid, price), tbdd) => treatPay(tid, price, tbdd)
      case (Ack(tid, price), tbdd) => treatAck(tid, price, tbdd)
    }

} /* object tp89 */
