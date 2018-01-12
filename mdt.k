/*

	Elaborato K-FRAMEWORK per il corso di LINGUAGGI - UniVR

 */


module MDT-SYNTAX

	/*
	 * TM states, lista degli stati della mdt
	 */
	syntax States ::= List{Int, ","}

	/*
	 * TM Final state declaration, stato finale (solamente 1)
	 */
	syntax FinalState ::= "Final" ":" Int
	
	/*
	 * TM Initial state declaration, stato iniziale (solamente 1)
	 */
	syntax InitialState ::= "Initial" ":" Int

	/*
	 * Configurazione del movimento della testina, left right or nothing 
	 */ 
	syntax Movement ::= "L" | "R" | "-"



    //syntax EXEC ::= "esecuzione"

	/*
	 * TM Transitions declaration, definizione della transizione. Inoltre una transizione è definita come due transizioni
	 *
	 * stato corrente , simbolo di input, stato successivo, simbolo di output, SPOSTAMENTO
	 *
	 */
	syntax Transition ::= "(" Int "," String "," Int "," String "," Movement ")"
							|	Transition Transition
						/* transizione 'concatenata' ad un altra transizione --> come devono essere scritte le transizioni*/

	/*
	 * Initial tape declaration, definizione del nastro, ovvero tutte le sequenze di simboli che deve eseguire
	 */
	syntax InitialTape ::= List{String, ","}

	/*
	 * Un programma è cosi definito, con le seguenti definizioni
	 */
	syntax Program ::= States FinalState InitialState Transition InitialTape

endmodule


module MDT
	imports MDT-SYNTAX

	/*
	 * transitions-configuration map key
	 */
	syntax K ::= "(" Int "," String ")"
	
	/*
	 * transitions-configuration map value
	 */
	syntax K ::= "(" Int "," String "," Movement ")"

	configuration 
	<T>
		<k> $PGM:Program </k>
		<tape> .Map </tape>
		<current-state> 0 </current-state>
		<current-position> 0 </current-position>
		<transitions> .Map </transitions>
		<states> .Set </states>
		<final-state> 0 </final-state>				/* messi a zero per inizializzare il valore dello stato iniziale */
		<initial-state> 0 </initial-state>
	</T>

	/*
	 * ~> indica l'ordine di valutazione
	 */
	rule SI:States F:FinalState I:InitialState TT:Transition Tape:InitialTape
		=> SI ~> F ~> I ~> TT ~> Tape [structural]

	/*
	 * valuta l'ordine delle transizioni, una transizione può essere concatenata da un'altra transizione
	 */
	rule T1:Transition T2:Transition => T1 ~> T2 [structural]

	/*
	 * Q e Qs 'appartengono' entrambi a States
	 * Q è lo stato attuale, mentre Qs è lo stato prossimo
	 */
	rule <k> ( Q, Qs:States => Qs ) ... </k> 		// 1 2 3 4 5 
		 <states> S:Set => S SetItem(Q) </states> 

	rule <k> .States => .K ... </k>

    /*
    leggo finalstate da Program, lo "svuoto" e inserisco in <finalstate> il valore letto
    */
	rule <k> (Final: I1:Int => .K) ...  </k>
	 <final-state> _ => I1 </final-state>

    /*
    stessa cosa per initialstate
    */
	rule <k> (Initial: I1:Int => .K) ...  </k>
     	<initial-state> _ => I1 </initial-state>
     	<current-state> _ => I1 </current-state>


    rule <k> ... ( C, Crs:InitialTape => Crs ) ... </k>
	    <tape> Tape:Map => Tape[P <- C] </tape>
        <current-position> P:Int => P +Int 1 </current-position>


    rule <k> ... ((I:Int, C:String, I2:Int, C2:String, M:Movement)) => "esecuzione" ... </k>
        <transitions> Trs:Map => Trs[(I, C) <- (I2, C2, M)] </transitions>

    rule <k> ... .InitialTape => .K ... </k>
         <current-position> _ => 0 </current-position>

    rule <k>  "esecuzione" => .K ... </k>
         <transitions> ... (Cs, In) |-> (Next:Int, Out:String, M:Movement) ... </transitions>
         <current-position> Cp:Int => Cp +Int 1 </current-position>
         <current-state> Cs:Int => Next </current-state>
         <tape> ... Cp |-> (In:String => Out) </tape>


	/*
	 * Equals with tape chars
	 */
	syntax Bool ::= K "==TapeChar" K [function]
	rule "*" ==TapeChar S:String => true
	rule S:String ==TapeChar "*" => true
	rule S1:String ==TapeChar S2:String => S1 ==String S2 when S1 =/=String "*" andBool S2 =/=String "*"

endmodule