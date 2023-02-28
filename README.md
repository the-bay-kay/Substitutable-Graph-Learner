# Substitutable-Graph-Learner
An implementation of Clark &amp; Eyraud's 2007 paper on SGL

    Substitutable Graph Learning - An Implementation
    Author : Katie Rischpater (katie.risc@gmail.com)

    Purpose: 
        This script is an implementation of the substitution 
        graphs and the algorithms detailed within Clark & Eyraud's 
        paper 'Polynomial Identification in the Limit of Substitutable
        Context-free Languages' (https://aclanthology.org/W16-5901.pdf)
        This script implements a modified version of Algorithms 1 & 2
        detailed in Section 3.1 - where those methods only consider a
        single string 'S', this algorithm parses the contexts for an
        entire body of sentences, which will be refered to as S-Prime.
    
    Files Included:
        - SLG-Learner.py:   The full script.  The pip modules networkx
                            and matplot are required.

        - SLG-Learner-LITE.py:  The script, minus the features that
                                require the modules above.

        - Sample Graphs/ : a directry of pre-rendered graph images.

        - Sample Texts/ : A collection of input texts to test the script.
        
        - SLG_LEARNER_CFG & SLG_LEARNER_GRAPH -EX: Two example outputs.

        - README.txt: This text!
        
    TO RUN:
        Using python3, run this code as you would any other script.
        For more on the various features, please run the script Using
        the --help flag.
