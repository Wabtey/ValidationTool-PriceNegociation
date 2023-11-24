package bank

/* The type of messages sent from the IHM, values are Scala Int */

abstract class ExtMessage
case class ExtPay(c:Int,m:Int,tid:Int,am:Int) extends ExtMessage
case class ExtAck(c:Int,m:Int,tid:Int,am:Int) extends ExtMessage
case class ExtCancel(c:Int,m:Int,tid:Int) extends ExtMessage
