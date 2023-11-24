package bank

import bank.observer.Observer
import bank.observer.Subject



object HOL {

trait equal[A] {
  val `HOL.equal`: (A, A) => Boolean
}
def equal[A](a: A, b: A)(implicit A: equal[A]): Boolean = A.`HOL.equal`(a, b)

def eq[A : equal](a: A, b: A): Boolean = equal[A](a, b)

} /* object HOL */

/* message type coming from Isabelle Theories */

abstract sealed class message
final case class Pay(a: (Nat.nat, (Nat.nat, Nat.nat)), b: Nat.nat) extends message
final case class Ack(a: (Nat.nat, (Nat.nat, Nat.nat)), b: Nat.nat) extends message
final case class Cancel(a: (Nat.nat, (Nat.nat, Nat.nat))) extends message

/* Nat Types coming from Isabelle Theories */


object Code_Numeral {

implicit def ord_integer: Orderings.ord[BigInt] = new Orderings.ord[BigInt] {
  val `Orderings.less_eq` = (a: BigInt, b: BigInt) => a <= b
  val `Orderings.less` = (a: BigInt, b: BigInt) => a < b
}

def integer_of_nat(x0: Nat.nat): BigInt = x0 match {
  case Nat.Nata(x) => x
}

def nat_of_integer(k: BigInt): Nat.nat =
  Nat.Nata(Orderings.max[BigInt](BigInt(0), k))

} /* object Code_Numeral */


object Orderings {

trait ord[A] {
  val `Orderings.less_eq`: (A, A) => Boolean
  val `Orderings.less`: (A, A) => Boolean
}
def less_eq[A](a: A, b: A)(implicit A: ord[A]): Boolean =
  A.`Orderings.less_eq`(a, b)
def less[A](a: A, b: A)(implicit A: ord[A]): Boolean = A.`Orderings.less`(a, b)

def max[A : ord](a: A, b: A): A = (if (less_eq[A](a, b)) b else a)

} /* object Orderings */

object Nat {
import /*implicits*/ Code_Numeral.ord_integer
abstract sealed class nat
final case class Nata(a: BigInt) extends nat

def equal_nata(m: nat, n: nat): Boolean =
  Code_Numeral.integer_of_nat(m) == Code_Numeral.integer_of_nat(n)

implicit def equal_nat: HOL.equal[nat] = new HOL.equal[nat] {
  val `HOL.equal` = (a: nat, b: nat) => equal_nata(a, b)
}

def less_nat(m: nat, n: nat): Boolean =
  Code_Numeral.integer_of_nat(m) < Code_Numeral.integer_of_nat(n)

def one_nat: nat = Nata(BigInt(1))
def zero_nat: nat = Nata(BigInt(0))

def less_eq_nat(m: nat, n: nat): Boolean =
  Code_Numeral.integer_of_nat(m) <= Code_Numeral.integer_of_nat(n)
  
def plus_nat(m: nat, n: nat): nat =
  Nata(Code_Numeral.integer_of_nat(m) + Code_Numeral.integer_of_nat(n))

def minus_nat(m: nat, n: nat): nat =
  Nata(Orderings.max[BigInt](BigInt(0),
                              Code_Numeral.integer_of_nat(m) -
                                Code_Numeral.integer_of_nat(n)))
  
} /* object Nat */


object Natural {

  def apply(numeral: BigInt): Natural = new Natural(numeral max 0)
  def apply(numeral: Int): Natural = Natural(BigInt(numeral))
  def apply(numeral: String): Natural = Natural(BigInt(numeral))

}

class Natural private (private val value: BigInt) {

  override def hashCode(): Int = this.value.hashCode()

  override def equals(that: Any): Boolean = that match {
    case that: Natural => this equals that
    case _ => false
  }

  override def toString(): String = this.value.toString

  def equals(that: Natural): Boolean = this.value == that.value

  def as_BigInt: BigInt = this.value
  def as_Int: Int = if (this.value >= scala.Int.MinValue && this.value <= scala.Int.MaxValue)
    this.value.intValue
  else sys.error("Int value out of range: " + this.value.toString)

  def +(that: Natural): Natural = new Natural(this.value + that.value)
  def -(that: Natural): Natural = Natural(this.value - that.value)
  def *(that: Natural): Natural = new Natural(this.value * that.value)

  def /%(that: Natural): (Natural, Natural) = if (that.value == 0) (new Natural(0), this)
  else {
    val (k, l) = this.value /% that.value
    (new Natural(k), new Natural(l))
  }

  def <=(that: Natural): Boolean = this.value <= that.value

  def <(that: Natural): Boolean = this.value < that.value

}


/* The bank object used in IHM */

class Bank(validator : TransValidator) extends Subject{
	var trace: List[ExtMessage]=List()
	var obs: Set[Observer]=Set()
	
	def addObserver(o:Observer)= {obs=obs + o}
	def removeObserver(o:Observer)={obs=obs - o}
	def update= obs.map((o:Observer)=> o.myNotify(this))
		
	def transListToString(l:List[((Nat.nat, (Nat.nat,Nat.nat)),Nat.nat)]):String=
	  l match {
	  case Nil => ""
	  case ((Nat.Nata(c), (Nat.Nata(m), Nat.Nata(i))),Nat.Nata(am))::rem => "(("+c+","+m+","+i+"),"+am+")\n"+transListToString(rem)
	}
	  
	def extMessageListToString(l:List[ExtMessage]):String=
	  l match {
	  case Nil => ""
	  case m::rem => (m.toString)+" "+extMessageListToString(rem)
	}
	
	def transToString=transListToString(validator.getValidTrans)
	def traceToString=
	  extMessageListToString(trace)
	// Pour convertir un ExtMessage en message on doit convertir des Int scala en Nat Isabelle 
	// 
	def extMessage2message(m:ExtMessage):message=
	  m match{
	  	case ExtPay(c,m,tid,am) => if (c>=0 && m>=0 && tid>= 0 && am>=0) Pay((Nat.Nata(c),(Nat.Nata(m),Nat.Nata(tid))),Nat.Nata(am)) else throw new IllegalArgumentException("Negative numbers for client, merchant or transaction")
	  	case ExtAck(c,m,tid,am) => if (c>=0 && m>=0 && tid>= 0 && am>=0) Ack((Nat.Nata(c),(Nat.Nata(m),Nat.Nata(tid))),Nat.Nata(am)) else throw new IllegalArgumentException("Negative numbers for client, merchant or transaction")
	  	case ExtCancel(c,m,tid) => if (c>=0 && m>=0 && tid>= 0) Cancel((Nat.Nata(c),(Nat.Nata(m),Nat.Nata(tid)))) else throw new IllegalArgumentException("Negative numbers for client, merchant or transaction")
	}
	  
	def traiter(m: ExtMessage):Unit={
	  try{
	  	validator.process(extMessage2message(m))
	  	trace= m::trace
	  	update
	  } 
	  	catch {
	  	  case e:IllegalArgumentException => ()
	  	}
	  	
	}
	
	
}