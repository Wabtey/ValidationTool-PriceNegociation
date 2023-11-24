package bank;

import java.awt.GridLayout;

import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JTextArea;
import javax.swing.JTextField;
import javax.swing.SwingUtilities;

import bank.action.SendCancel;
import bank.action.SendClient;
import bank.action.SendMerchant;
import bank.observer.Observer;
import bank.observer.Subject;




public class Ihm extends JFrame implements Observer {

	// composants de la fenetre

	private JLabel lc1= new JLabel("Client id");
	private JLabel lc2= new JLabel("Merchant id");
	private JLabel lc3= new JLabel("Transaction id");
	private JLabel lc4= new JLabel("Amount");

	private JLabel lm1= new JLabel("Cient id");
	private JLabel lm2= new JLabel("Merchant id");
	private JLabel lm3= new JLabel("Transaction id");
	private JLabel lm4= new JLabel("Amount");
	private JLabel none1= new JLabel(" ");
	private JLabel none2= new JLabel(" ");

	private JLabel ltrans= new JLabel("Transactions accepted by the Bank");
	private JLabel ltrace= new JLabel("Full messages trace");
	
	private JTextField zoneC1;
	private JTextField zoneC2;
	private JTextField zoneC3;
	private JTextField zoneC4;

	private JTextField zoneM1;
	private JTextField zoneM2;
	private JTextField zoneM3;
	private JTextField zoneM4;

	private JTextArea zoneB;	
	private JTextArea zoneTrace;
	
	private JPanel panelExt;
	private JPanel panelCM;
	private JPanel panelB;
	private JPanel panelTrace;
	private JPanel panelButtonM;
	
	private JButton buttonC;
	private JButton buttonM;
	private JButton buttonCancel;
	
	private Bank bank= new Bank(new validator.<LE_NOM_DE_VOTRE_BINOME>.ConcreteValidator());

	
	public Ihm() { 
		this.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
		this.setTitle("Transaction Simulator");		

		buttonC= new JButton(new SendClient("Client sends...",this));
		buttonM= new JButton(new SendMerchant("Merchant sends...",this));
		buttonCancel= new JButton(new SendCancel("Merchant cancels",this));
	
		zoneC1 = new JTextField(5);
		zoneC2 = new JTextField(5);
		zoneC3 = new JTextField(5);
		zoneC4 = new JTextField(5);

		zoneM1 = new JTextField(5);		
		zoneM2 = new JTextField(5);
		zoneM3 = new JTextField(5);
		zoneM4 = new JTextField(5);

		
		zoneB = new JTextArea("",10,30);
		zoneB.setEditable(false);
		zoneTrace = new JTextArea("",10, 30);
		zoneTrace.setEditable(false);
		
		// sauts de lignes automatiques dans les zoneB et zoneTrace
		zoneB.setLineWrap(true);  
		zoneTrace.setLineWrap(true);  
		zoneB.setWrapStyleWord(true);
		zoneTrace.setWrapStyleWord(true);
		
		panelExt = new JPanel();
		panelCM = new JPanel();
		panelB= new JPanel();
		panelTrace= new JPanel();
		panelButtonM= new JPanel();
		
		//panel.setLayout(new FlowLayout()); // avec une méthode de placement automatique
		
		panelExt.setLayout(new GridLayout(3,1));
		panelCM.setLayout(new GridLayout(4,5));
		panelB.setLayout(new GridLayout(2,1));
		panelTrace.setLayout(new GridLayout(2,1));
		panelButtonM.setLayout(new GridLayout(2,1));
		
		panelCM.add(lc1);
		panelCM.add(lc2);
		panelCM.add(lc3);
		panelCM.add(lc4);
		panelCM.add(none1);
		panelCM.add(zoneC1);
		panelCM.add(zoneC2);
		panelCM.add(zoneC3);
		panelCM.add(zoneC4);
		
		panelCM.add(buttonC);

		panelCM.add(lm1);
		panelCM.add(lm2);
		panelCM.add(lm3);
		panelCM.add(lm4);
		panelCM.add(none2);

		panelCM.add(zoneM1);
		panelCM.add(zoneM2);
		panelCM.add(zoneM3);
		panelCM.add(zoneM4);
		
		panelButtonM.add(buttonM);
		panelButtonM.add(buttonCancel);
		panelCM.add(panelButtonM);

		panelB.add(ltrans);
		panelB.add(zoneB);
		
		panelTrace.add(ltrace);
		panelTrace.add(zoneTrace);
		
		panelExt.add(panelCM);
		panelExt.add(panelB);
		panelExt.add(panelTrace);
		
		// on associe le panel à la fenêtre d'Ihm
		this.setContentPane(panelExt);
		bank.addObserver(this);
	}

	
	
	public void sendClient(){
		try{
			bank.traiter(new ExtPay(Integer.parseInt(zoneC1.getText()),
									Integer.parseInt(zoneC2.getText()),
									Integer.parseInt(zoneC3.getText()),
									Integer.parseInt(zoneC4.getText())));
		} catch (NumberFormatException e) {}
		}
	
	public void sendMerchant(){
		try{
			bank.traiter(new ExtAck(Integer.parseInt(zoneM1.getText()),
									Integer.parseInt(zoneM2.getText()),
									Integer.parseInt(zoneM3.getText()),
									Integer.parseInt(zoneM4.getText())));
		} catch (NumberFormatException e) {}
		}
	
	public void cancel(){
		try{
			bank.traiter(new ExtCancel(Integer.parseInt(zoneM1.getText()),
									Integer.parseInt(zoneM2.getText()),
									Integer.parseInt(zoneM3.getText())));
		} catch (NumberFormatException e) {}
	}
	
	
	public void myNotify(Subject s){
		zoneB.setText((String)((Bank) s).transToString());
		zoneTrace.setText((String)((Bank) s).traceToString());
	}
	
	
	public static void main(String[] args) {
		SwingUtilities.invokeLater(new Runnable(){ 
		public void run(){ 		
			    Ihm ihm = new Ihm();
			    ihm.setSize(700, 350);
				ihm.setVisible(true); 
				ihm.pack();
			   }
		}); 
	}
}
