# Validation Tool for a Price Negociation web application

[tp8-10.pdf](tp89.pdf), [tp8-10.thy](http://people.irisa.fr/Thomas.Genet/ACF/TPs/tp89.thy), [TP89_ACF.zip](http://people.irisa.fr/Thomas.Genet/ACF/TPs/TP89_ACF.zip), [table.thy](http://people.irisa.fr/Thomas.Genet/ACF/TPs/table.thy):
Students design a validation tool for a price negociation web application.
A merchant and a client send messages to the validation tool to negociate a price.
A price is validated if a price proposed by a client is superior or equal to a price proposed by the merchant.
In the end, the list of validated should be correct.
As with all protocols, more complex than it seems at first glance.
They define the functions, check the 9 properties and export the Scala code.
All the validations tools of all students are then deployed on a web site so that all students can attack all validation tools and report on the attacks found.
Proofs are optional. To carry out the proofs, you can get inspiration from this short [video (in french)](https://video.univ-rennes1.fr/videos/principes-de-preuve-avances-en-isabellehol/) with the [pc.thy](http://people.irisa.fr/Thomas.Genet/ACF/TPs/pc.thy) Isabelle/HOL file.
For this lab session a list of relevant intermediate lemmas (in french) is also provided:
[tp8-10proof.thy](http://people.irisa.fr/Thomas.Genet/ACF/TPs/tp89proof.thy).
