package bank.observer

trait Subject {
	def addObserver(o:Observer):Unit
	def removeObserver(o:Observer):Unit
	def update:Unit
}