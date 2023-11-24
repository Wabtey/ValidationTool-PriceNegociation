package validator.LE_NOM_DE_VOTRE_BINOME

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
  // TODO
  def getValidTrans = List()
}

// Objets utile pour pouvoir compiler avant la première exportation
// ...à supprimer une fois que votre export aura été fait.
object tp89 {
  sealed trait message
  case class Pay(a: (Nat.nat, (Nat.nat, Nat.nat)), b: Nat.nat) extends message
  case class Ack(a: (Nat.nat, (Nat.nat, Nat.nat)), b: Nat.nat) extends message
  case class Cancel(a: (Nat.nat, (Nat.nat, Nat.nat))) extends message
}

object Nat {
  sealed trait nat
  case class Nata(a: BigInt) extends nat
}
