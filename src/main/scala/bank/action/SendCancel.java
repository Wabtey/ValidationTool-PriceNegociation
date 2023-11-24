package bank.action;

import java.awt.event.ActionEvent;
import javax.swing.AbstractAction;

import bank.Ihm;



public class SendCancel extends AbstractAction{
	private Ihm ihm;
	public SendCancel(String nom, Ihm ihm){
		super(nom);
		this.ihm=ihm;
	}
	
	public void actionPerformed(ActionEvent e) {
		ihm.cancel();
	}
}

