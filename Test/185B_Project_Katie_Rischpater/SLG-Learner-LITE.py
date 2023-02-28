#!/usr/bin/python3
'''
    Substitutable Graph Learning - An Implementation
    Author : Katie Rischpater (katie.risc@gmail.com)
    Updated : 6-15-22

    Purpose: 
        This script is an implementation of the substitution 
        graphs and the algorithms detailed within Clark & Eyraud's 
        paper 'Polynomial Identification in the Limit of Substitutable
        Context-free Languages' (https://aclanthology.org/W16-5901.pdf)
        This script implements a modified version of Algorithms 1 & 2
        detailed in Section 3.1 - where those methods only consider a
        single string 'S', this algorithm parses the contexts for an
        entire body of sentences, which will be refered to as S-Prime.
        In order to implement this modified algorithm, an algorithm for 
        generating Substitution Graphs in this manner has been created.
        This can be seen in the __init__() method, and the modified
        algorithm can be found in algorithm_one_two()

    TO RUN: This is the LITE version of the script - no external
        modules are required, however the --visualize feature has
        been ommited.
    
    Comment Notation:
        :       "such that" (not to be confused with the dict {a : b})
        0.0     "Section 0.0 of Clark & Eyraud"
        ||      "Divider between datatype & Explanation"
        Sig.    "Sigma, the given alphabet of a Grammar / Graph"
        |X|     "Cardinality of a set"
            
'''


# stdlib imports
import argparse, sys, math, re
from datetime import datetime

# Command Line Interractions
help_splash = '''Usage: SLG-Learner [OPTION]... [FILE]
    Given a string of sentences S, from an infile or from a
    built-in data structure, generate a Substitution Graph
    from which a Context-Free-Grammar is generated.
'''

# Global Definitions

parser = argparse.ArgumentParser(description=help_splash, 
    formatter_class=argparse.RawTextHelpFormatter)

parser.add_argument('-i', '--infile', nargs='?', 
    type=argparse.FileType('r'),help='Input File : each \"word\" is '
        'parsed by taking the characters between periods, and each '
        'symbol is a real word.') 

parser.add_argument('-t', '--toy', action='store_true',
     default=False, help='Input File : each line '
        'is a \"word\", and each symbol is an individual char'
        ': e.x., toy grammars \"abba\" ')

parser.add_argument('-p', '--print', action='store_true',
    default=False, help='Send output to console'
    'rather than separate output files.')

args = parser.parse_args()

TIMESTAMP = datetime.now().strftime('%H_%M_%S')
GRAPH_FILE = './SLG_Learner_GRAPH_' + TIMESTAMP + '.txt'
CFG_FILE = './SLG_Learner_CFG_' + TIMESTAMP + '.txt'

# Function Definitions

def handle_arguments():
    if not len(sys.argv) > 1:
        sys.stdout = open(GRAPH_FILE, 'w')
        return None
    if args.toy and not args.infile:
        print("Please specify an infile!")
        exit()
    if not args.print:
        sys.stdout = open(GRAPH_FILE, 'w')
    if args.infile:
        with open(args.infile.name) as f:
            s = f.read()
        if args.toy: # Toy Grammar
            s = s.splitlines()
        else:
            s = re.sub('[^a-zA-Z\.\s]', '', s)
            s = re.split('\.', s)
            s_temp = []
            for w in s:
                s_temp.append(tuple(w.split()))
            s = s_temp
        while () in s:
            s.remove(())
        return s
    return None

# I like my nice formatting...
def pretty_print(container, title, is_grammar = False):
    print('\n' + title + '\n')
    for item in container:
        if is_grammar:
            print(set(item))
        else:
            print(item)

# SG(S) = (V, E) - Defined in 3.0
class Substitution_Graph:
    # s = ['strings'] ' || e.g., the toy ['abba'], or 
    # [['The','man','walked']] for full words
    def __init__(self, name, s):
        contexts = {} # {(l, r) : {u, v, ...}} || edge (u, v) for strs
                      # 'lur' 'lvr' in Sig.
        # This is the quadratic bottlneck to the graph 
        # creation; we need to check each 'word' (or sentence,
        # depending on the corpus) in the sequence S, and each W must
        # be divided into substrings. - 7.1, Par 1 
        for word in s:
            for i in range(0, len(word)):
                for j in range(0, len(word)-i):
                    l = word[0:j]
                    u = word[j:j+i+1]
                    r = word[j+i+1:]
                    con = (l,r)
                    if con not in contexts:
                        contexts[con] = {u}
                    else:
                        contexts[con].add(u)                
        self.name = name
        self.contexts = contexts
        # Generate Components == eq:
        eq_classes = set()
        for v in self.get_vertices():
            eq = {v}
            for c in contexts:
                # print('Checking ', v, ' in ', contexts[c])
                if v in contexts[c] and len(contexts[c]) > 1:
                    eq.update(contexts[c])
            eq_classes.add(frozenset(eq)) # why must this freeze python
        self.eq_classes = eq_classes
    def get_eq(self, sym):
        for e in self.eq_classes:
            if sym in e: 
                return e
        return None # This should NEVER happen :)
    def get_vertices(self):
        alphabet = set()
        for c in self.contexts:
            for u in self.contexts[c]:
                alphabet.add(u)
        return alphabet
    def get_edges(self):
        edges = set()
        for c in self.contexts:
            # If component is greater than a single vertex, generate the
            # edges for the coresponding congruence class
            c_class = list(self.contexts[c])
            if(len(c_class) > 1):
                for i in range(0, len(c_class) - 1):
                    pair = (c_class[i], c_class[i+1])
                    edges.add(pair)
        return edges
    def print_formal(self):
        print('# ', self.name, ' #\n')
        pretty_print(self.get_vertices(), 'Vertices: ')
        pretty_print(self.get_edges(), 'Edges: ')
    def print_context(self):
        print("\n# ", self.name, " Contexts #")
        for c in self.contexts:
            if len(c) > 1: # Set to 0 to see all non-comp contexts
                print(c, ':', self.contexts[c], '\n')

# G = <S, V, P, S> || 2.0, Definition 1
# S = Alphabet, V = NonTerminals,
# P = Finite Production Rules
# S = S is contained in V, subset of start syms
class Grammar:
    def __init__(self, name, alphabet, variables, prods, starts):
        self.name = name
        self.alphabet = alphabet # {'x'} || ('substr')
        self.non_terminals = variables # {'XP'} || {frozenset()}
        self.starts = starts # {'SHN'} || S node, {[]}
        self.productions = prods # {( X ,(lu,r) )} || Rules S -> DP TP
    # Because the ProdRules are more important, this is seperate
    def print_rules(self):
        print('\n [+] Rules [+]  \n')

        for rhs in self.productions:
            for lhs in self.productions[rhs]:
                if len(lhs) == 1:
                    print(set(rhs), '-->', lhs)
                # This is for legibility; no 'frozenSet' in output
                else:
                    r1 = lhs[0]
                    if r1 is not None:
                        r1 = set(r1)
                    r2 = lhs[1]
                    if r2 is not None:
                        r2 = set(r2)
                    print(set(rhs), '-->', r1, ' + ', r2)
                
    # I like pretty formatting...
    def print_grammar(self):
        print('\n #  CFG: ', self.name, ' #\n')
        pretty_print(set(self.alphabet), '[+] Alphabet [+]')
        pretty_print(self.non_terminals, 
            '[+] Non-Terminal Nodes [+]', True)
        pretty_print(self.starts, '[+] Starting Nodes [+]')
        self.print_rules()
        
# Note: For a CFG, S -> (Empty, Empty)
# and P is a subset of (V * X (S U V)+)

# Converts a Substitution Graph to a CFG - 3.1
# For this Alg; S-prime ~= S, however S' will contain the sum of all
# strings within the original input corpus.  As such, the CFG
# S-hat is : |S-hat| = |S|. 
def algorithm_one_two(graph, s_prime):
    components = graph.eq_classes
    # Sigma
    alphabet = graph.get_vertices()
    # Mapping V -> V_hat:
    v_hat = set()
    for v in components:
        v_hat.add(v) # unfreeze for legibility :)
    # Mappping Sigma -> P  || this is rule type 1, e.g. A --> 'a'
    p_hat = dict()
    for u in alphabet:
        component = graph.get_eq(u)
        if len(u) == 1:
            if component not in p_hat:
                p_hat[component] = {u}
            else:
                p_hat[component].add(u)
        else:
            for i in range(1, len(u)):
                # For whatever reason, these need to be seperate
                # because of python frozen sets... ):
                v = u[0:i] 
                vnext = graph.get_eq(v)
                w = u[i:]
                wnext = graph.get_eq(w)
                to_be_added = (vnext, wnext)
                if component not in p_hat:
                    p_hat[component] = {to_be_added}
                else:
                    p_hat[component].update({to_be_added})
    # Mapping null-contexts to S-Hat, adding them to prod. rules
    s_hat = set()
    for s in s_prime: # prodRules will be req'd?
        s_hat.add(s)
    zero_reversible_cfg = Grammar(graph.name, alphabet, v_hat, p_hat, s_hat)
    return zero_reversible_cfg

def print_g_info(graph, string = ''):
    x = '\n'
    for i in range(0,79):
        x += '='
    print(x, '\n')
    graph.print_formal()
    graph.print_context()

# Main
def builtin_tests():
    str_1 = ['abbcbba', 'abcba', 'aacaa', 'aaacaaa', 'bbbcbbb']
    sg_1 = Substitution_Graph('SG_1', str_1) # Toy Grammar 1
    cfg_1 = algorithm_one_two(sg_1, str_1)

    str_2 = (
        ('the','dog','ran'),
        ('the','cat','ran'),
        ('the','cat','quickly','walked'),
        ('the','cat','slowly','walked'),
    )
    sg_2 = Substitution_Graph('SG_2', str_2)
    cfg_2 = algorithm_one_two(sg_2, str_2)

    print_g_info(sg_1, str_1)
    print_g_info(sg_2, str_2)

    if not args.print:
        sys.stdout.close()
        sys.stdout = open(CFG_FILE, 'w')
    
    cfg_1.print_grammar()
    cfg_2.print_grammar()

def main():
    s = handle_arguments()
    # if no infiles given, just run tests with builtins
    if s is None:
        builtin_tests()
        return 0

    sg = Substitution_Graph(args.infile.name, s)
    zr_cfg = algorithm_one_two(sg, s)

    sg.print_formal()
    if not args.print:
        sys.stdout.close()
        sys.stdout = open(CFG_FILE, 'w')
    zr_cfg.print_grammar()

if __name__ == '__main__':
    main()