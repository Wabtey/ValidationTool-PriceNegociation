package bank.observer

trait Observer {
	def myNotify(s: Subject):Unit
}