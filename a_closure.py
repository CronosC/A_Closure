import numpy as np
import random
import time
from itertools import chain, combinations
from os.path import exists
import sys
from copy import deepcopy
sys.setrecursionlimit(5000)

class solver:
    calculus = None
    qcsp = None

    # other
    debug = False
    timed = False
    allow_reading_existing = True
    timer = time.perf_counter()

    def __init__(self, qcsp):
        self.set_qcsp(qcsp)

    def set_calculus(self, calculus):
        self.calculus = calculus

    def set_qcsp(self, qcsp):
        self.qcsp = qcsp
        self.calculus = qcsp.calculus

    def a_closure_1(self):
        self.timer_start()
        qcsp_table = self.qcsp.qcsp_table
        nodes_number = self.qcsp.nodes_number
        s = True
        while s:
            s = False
            for i in range(nodes_number):
                for j in range(nodes_number):
                    for k in range(nodes_number):
                        C_i_k = qcsp_table[i][k]
                        C_i_j = qcsp_table[i][j]
                        C_j_k = qcsp_table[j][k]
                        C_star_i_k = self.calculus.intersect(C_i_k, self.calculus.compose(C_i_j, C_j_k))
                        if C_i_k != C_star_i_k:
                            qcsp_table[i][k] = C_star_i_k
                            s = True

                            if C_star_i_k == self.calculus.empty_relation:
                                self.timer_end("time to find empty relation in qcsp (a closure 1.0)")
                                return qcsp_table
        self.timer_end("time to run a-closure 1.0")
        return qcsp_table

    def a_closure_2_no_ref(self):
        self.timer_start()
        qcsp_table = self.qcsp.qcsp_table
        nodes_number = self.qcsp.nodes_number
        Queue = []
        # initialize queue with all edges
        for i in range(nodes_number):
            for j in range(nodes_number):
                Queue.append((i, j))

        while len(Queue) > 0:
            edge = Queue.pop(0)
            # iterate over all possible triangles
            for k in range(nodes_number):
                if k != j and k != i:
                    i = edge[0]
                    j = edge[1]
                    # first as i -> j -> k, i -> k
                    C_i_k = qcsp_table[i][k]
                    C_i_j = qcsp_table[i][j]
                    C_j_k = qcsp_table[j][k]
                    C_star_i_k = self.calculus.intersect(C_i_k, self.calculus.compose(C_i_j, C_j_k))
                    if C_i_k != C_star_i_k:
                        qcsp_table[i][k] = C_star_i_k
                        print("reduced", C_i_k, " to ", C_star_i_k)
                        if (i, k) not in Queue:
                            Queue.append((i, k))
                        if C_star_i_k == self.calculus.empty_relation:
                            self.timer_end("time to find empty relation in qcsp (a closure 2.0)")
                            return qcsp_table
                    # then as k -> i -> j, k -> j
                    C_k_j = qcsp_table[k][j]
                    C_k_i = qcsp_table[k][i]
                    # C_i_j stays the same
                    C_star_k_j = self.calculus.intersect(C_k_j, self.calculus.compose(C_k_i, C_i_j))
                    if C_k_j != C_star_k_j:
                        qcsp_table[k][j] = C_star_k_j
                        print("reduced", C_k_j, " to ", C_star_k_j)
                        if (k, j) not in Queue:
                            Queue.append((k, j))
                    if C_star_k_j == self.calculus.empty_relation:
                        self.timer_end("time to find empty relation in qcsp (a closure 2.0)")
                        return qcsp_table
        self.timer_end("time to run a-closure 2.0")
        return qcsp_table

    def a_closure_2(self, qcsp_table, Queue=[]):
        self.timer_start()
        nodes_number = len(qcsp_table[0])

        if Queue == []:
            # initialize queue with all edges
            for i in range(nodes_number):
                for j in range(nodes_number):
                    Queue.append((i, j))

        while len(Queue) > 0:
            edge = Queue.pop(0)
            i = edge[0]
            j = edge[1]
            # iterate over all possible triangles
            for k in range(nodes_number):
                if k != j and k != i:
                    i = edge[0]
                    j = edge[1]
                    # first as i -> j -> k, i -> k
                    C_i_k = qcsp_table[i][k]
                    C_i_j = qcsp_table[i][j]
                    C_j_k = qcsp_table[j][k]
                    C_star_i_k = self.calculus.intersect(C_i_k, self.calculus.compose(C_i_j, C_j_k))
                    if C_i_k != C_star_i_k:
                        qcsp_table[i][k] = C_star_i_k
                        print("reduced", C_i_k, " to ", C_star_i_k)
                        if (i, k) not in Queue:
                            Queue.append((i, k))
                        if C_star_i_k == self.calculus.empty_relation:
                            self.timer_end("time to find empty relation in qcsp (a closure 2.0)")
                            return qcsp_table
                    # then as k -> i -> j, k -> j
                    C_k_j = qcsp_table[k][j]
                    C_k_i = qcsp_table[k][i]
                    # C_i_j stays the same
                    C_star_k_j = self.calculus.intersect(C_k_j, self.calculus.compose(C_k_i, C_i_j))
                    if C_k_j != C_star_k_j:
                        qcsp_table[k][j] = C_star_k_j
                        print("reduced", C_k_j, " to ", C_star_k_j)
                        if (k, j) not in Queue:
                            Queue.append((k, j))
                    if C_star_k_j == self.calculus.empty_relation:
                        self.timer_end("time to find empty relation in qcsp (a closure 2.0)")
                        return qcsp_table
        self.timer_end("time to run a-closure 2.0")
        return qcsp_table

    def refinement_search_1(self, qcsp_table):
        self.timer_start()
        nodes_number = len(qcsp_table[0])
        qcsp_table_star = self.a_closure_2(deepcopy(qcsp_table))

        # check if there is an empty relation in the new qcsp
        if qcsp_table_star.min == self.calculus.empty_relation:
            return false

        # check if all relations are already base relations
        if (np.isin(qcsp_table_star, calculus.base_relations)).all():
            return true

        # refine to base relation
        # chose one that isn't already base relation
        indices_without_base_relation = np.transpose(np.isin(qcsp_table_star, calculus.base_relations)) # as boolean, True where base rel
        indices_without_base_relation = np.invert(indices_without_base_relation).nonzero() # Invert boolean, then get locations of Trues

        i = indices_without_base_relation[0][0]
        j = indices_without_base_relation[1][0]
        Cij = qcsp_table[i][j]
        for base_rel in self.calculus.base_relations:
            if self.calculus.intersect(Cij, base_rel):
                Cij = base_rel
                qcsp_table_star[i][j] = Cij
                qcsp_table_star[j][i] = self.calculus.converse(Cij)
                if self.refinement_search_1(deepcopy(qcsp_table_star)):
                    return True
        return False



    def timer_start(self):
        if self.timed:
            self.timer = time.perf_counter()

    def timer_end(self, text):
        if self.timed:
            time_taken = time.perf_counter() - self.timer
            print("[" + "{:.4f}".format(time_taken) + "s]", text)


class qcsp:
 
    qcsp_table = None
    calculus = None

    # info
    nodes_number = None

    # other
    debug = False
    timed = False
    allow_reading_existing = True
    timer = time.perf_counter()

    def __init__(self, path, calculus, debug=False, timed=False, allow_reading_existing=True):
        self.debug = debug
        self.timed = timed
        self.allow_reading_existing = allow_reading_existing
        self.calculus = calculus
        self.timer_start()
        self.read_qcsp(path)
        self.timer_end("finished reading qcsp")

    def read_qcsp(self, path):
        with open(path) as qcsp_file:
            lines = qcsp_file.readlines()
            
            # filter out comments
            for line in lines:
                if line.find('#')!=-1:
                    line = line[:line.find('#')-1]

            self.nodes_number = int(lines[0][:lines[0].find("#")].replace(" ", "").replace("\n", ""))
            self.qcsp_table = np.full((self.nodes_number, self.nodes_number), self.calculus.universal_relation, dtype=int)
            for edge in lines[1:len(lines) - 1]:
                edge = edge.replace("\n", "")
                node1 = int(edge[:edge.find(" ") + 1]) # read first node
                edge = edge[edge.find(" ") + 1:] # remove first node
                node2 = int(edge[:edge.find(" ")]) # read second node
                edge = edge[edge.find(" ") + 1:] # remove second node
                edge = edge.replace("(", "").replace(")", "").lstrip(" ").rstrip(" ")
                edge = self.calculus.order_agnostic_relation_text_to_num_conversion(edge)
                self.qcsp_table[node1][node2] = edge
                if self.debug:
                    self.print_edge(node1, node2)

            if self.debug:
                print("nodes found:", self.nodes_number)
                print("relations total:", self.qcsp_table.size)

    def timer_start(self):
        self.timer = time.perf_counter()

    def timer_end(self, text):
        time_taken = time.perf_counter() - self.timer
        print("[" + "{:.4f}".format(time_taken) + "s]", text)

    def print_edge(self, a, b):
        edge = self.calculus.relations_num_to_text[self.qcsp_table[a][b]]
        #print("(", a, ")   ", edge, "   (", b, ")")
        print(a, b, "  ", edge)
        
    def print_qcsp(self):
        for i in range(self.nodes_number):
            for j in range(self.nodes_number):
                if i < j:
                    self.print_edge(i, j)
            
class calculus:
    # info
    base_relations_number = 0
    base_relations = []
    complex_relations = [] # relations that are not base relations

    # transformation lookup tables
    relations_num_to_text = {}
    relations_text_to_num = {}

    # operation tables
    converse_table = None
    composition_table = None

    # special relations
    identity_relation = None
    empty_relation = None
    universal_relation = None

    # other
    debug = False
    timed = False
    allow_reading_existing = True
    timer = time.perf_counter()

    def __init__(self, path, debug=False, timed=False, allow_reading_existing=True):
        self.debug = debug
        self.timed = timed
        self.allow_reading_existing = allow_reading_existing
        self.read_calculus(path)

    def read_calculus(self, path):
        self.timer_start()
        self.read_relations_file(path)
        self.timer_end("time to read relations file & construct necessary data structures")

        self.timer_start()
        self.read_identity_file(path)
        self.timer_end("time to read identity file & construct necessary data structures")

        self.timer_start()
        self.read_converse_file(path)
        self.timer_end("time to read converse file & construct necessary data structures")

        self.timer_start()
        self.read_composition_file(path)
        self.timer_end("time to read composition file & construct necessary data structures")

    def read_relations_file(self, path):
        self.debug_print("\n[RELATIONS FILE]")
        with open(path + ".relations") as relations_file:
            lines = relations_file.readlines()
            for line in lines:
                rel_text = line.replace("\n", "")
                rel_num = (1<<self.base_relations_number)
                self.relations_text_to_num[rel_text] = rel_num
                self.relations_num_to_text[rel_num] = rel_text
                self.base_relations_number+=1
                self.base_relations.append(rel_num)

        # then construct the powerset of base relations as list of tuples
        all_relations = list(chain.from_iterable(combinations(self.base_relations, r) for r in range(len(self.base_relations)+1)))
        assert len(all_relations) == 2**self.base_relations_number
        # subtract existing relations from all relations to get complex relations
        all_relations = list(set(all_relations) - set(self.base_relations))
        # add missing relations to our lookups
        for rel_tuple in all_relations:
            rel_num = 0
            rel_text = ""
            for rel_component in rel_tuple:
                rel_num = self.union(rel_num, rel_component)
                if rel_text == "":
                    rel_text = self.relations_num_to_text[rel_component]
                else:
                    rel_text = rel_text + " " + self.relations_num_to_text[rel_component]
            self.relations_num_to_text[rel_num] = rel_text
            self.relations_text_to_num[rel_text] = rel_num
            self.complex_relations.append(rel_num)

        # one special case, the empty relation:
        self.relations_num_to_text[0] = "ø"
        self.relations_text_to_num["ø"] = 0

        # shorthands
        self.empty_relation = 0
        self.universal_relation = (2**self.base_relations_number)-1


        assert len(self.relations_num_to_text) == 2**self.base_relations_number
        if self.debug:
            print("number of base relations: ", self.base_relations_number)
            print("base relations: ")
            for br in self.base_relations:
                self.print_relation(br)
            print("total number of relations: ", len(self.relations_num_to_text))
            print("come constructed relations: ")
            for i in range(10):
                rel = random.randint(0, self.universal_relation)
                self.print_relation(rel)
            print("empty relation:")
            self.print_relation(self.empty_relation)
            print("universal relation:")
            self.print_relation(self.universal_relation)

    def read_identity_file(self, path):
        self.debug_print("\n[IDENTITY FILE]")
        with open(path + ".identity") as identity_file:
            self.identity_relation = self.relations_text_to_num[identity_file.readline().replace("\n", "").replace(" ", "")]

        self.debug_print("identity relation:")
        if self.debug:
            self.print_relation(self.identity_relation)

    def read_converse_file(self, path):
        self.debug_print("\n[CONVERSE FILE]")
        # prep:
        self.converse_table = np.zeros(len(self.relations_num_to_text), dtype=int)
        # first read the converses of base relations, which are given in file
        with open(path + ".conv") as converse_file:
            lines = converse_file.readlines()
            for line in lines:
                line = line.replace(" ", "").replace("\n", "").split("::")
                self.converse_table[self.relations_text_to_num[line[0]]] = self.relations_text_to_num[line[1]]

        # then construct the remaining converses from the simple relation converses
        for cr in self.complex_relations:
            for br in self.base_relations:
                if(cr & br)>=1:
                    self.converse_table[cr] = self.union(self.converse_table[cr], self.converse_table[br])

        self.debug_print("construction of converse table done")
        self.debug_print("base converses:")
        if self.debug:
            for br in self.base_relations:
                self.print_converse(br)
        self.debug_print("some constructed converses:")
        if self.debug:
            for i in range(10):
                random_rel = random.randint(0, self.universal_relation)
                self.print_converse(random_rel)

    def read_composition_file(self, path):
        self.debug_print("\n[COMPOSITION FILE]")
        # prep
        self.composition_table = np.zeros((len(self.relations_num_to_text), len(self.relations_num_to_text)), dtype=int)

        if exists(path + "_composition_matrix.npy") and self.allow_reading_existing:
            self.debug_print(" loading composition table from file..")
            self.composition_table = np.load(path + "_composition_matrix.npy")
        else:
            self.debug_print(" calculating composition table..")
            # read the simple compositions from file
            with open(path + ".comp") as composition_file:
                lines = composition_file.readlines()
                for line in lines:
                    line = line.replace("::", ":").replace(")", "").replace("(", "").split(" : ")
                    line[0] = self.relations_text_to_num[line[0].replace(" ", "")]
                    line[1] = self.relations_text_to_num[line[1].replace(" ", "")]
                    line[2] = self.order_agnostic_relation_text_to_num_conversion(line[2].replace("\n", "").lstrip(" ").rstrip(" "))
                    self.composition_table[line[0]][line[1]] = line[2]
            # construct the remaining complex compositions
            for r1 in (self.base_relations + self.complex_relations):
                for r2 in (self.base_relations + self.complex_relations):
                    if r2 >= r1:
                        self.composition_table[r1][r2] = self.compose_calculate(r1, r2)
                        self.composition_table[r2][r1] = self.composition_table[r1][r2]
            # save for later
            np.save(path + "_composition_matrix.npy", self.composition_table)

        # debug info
        self.debug_print("construction of composition table done")
        self.debug_print("some example compositions:")
        if self.debug:
            for i in range(10):
                random_rel1 = random.randint(0, self.universal_relation)
                random_rel2 = random.randint(0, self.universal_relation)
                self.print_composition(random_rel1, random_rel2)



    def debug_print(self, str):
        if self.debug:
            print(str)

    def timer_start(self):
        self.timer = time.perf_counter()

    def timer_end(self, text):
        time_taken = time.perf_counter() - self.timer
        print("[" + "{:.4f}".format(time_taken) + "s]", text)

    def print_relation(self, rel_num, end="\n"):
        print("(", self.relations_num_to_text[rel_num], ")", end=end)

    def print_converse(self, rel_num, end="\n"):
         self.print_relation(rel_num, end=" "*5)
         print(" :: ", end= " "*5)
         self.print_relation(self.converse_table[rel_num], end=end)

    def print_composition(self, rel_num1, rel_num2, end="\n"):
         self.print_relation(rel_num1, end=" "*5)
         print("  :  ", end= " "*5)
         self.print_relation(rel_num2, end=" "*5)
         print("  ::  ", end= " "*5)
         self.print_relation(self.compose(rel_num1, rel_num2), end=end)

    def order_agnostic_relation_text_to_num_conversion(self, text):
        text = text.split(" ")
        rel_num = 0
        for part in text:
            rel_num = self.union(rel_num, self.relations_text_to_num[part])
        return rel_num

    def show_relations(self):
        for value in self.relations_num_to_text:
            print(str(value) + ":", self.relations_num_to_text[value])

    def compose(self, A, B):
        return self.composition_table[A, B]

    def compose_calculate(self, A, B):
        rel_num = 0
        for a in self.base_relations:
            if (a & A):
                for b in self.base_relations:
                    if (b & B):
                        rel_num = self.union(rel_num, self.compose(a, b))
                        if rel_num == self.universal_relation:
                            return rel_num
        return rel_num

    def compose_calculate_alternative_2(self, A, B):
        rel_num = 0
        for a in range(self.base_relations_number):
            if ((1<<a) & A) > 0:
                for b in range(self.base_relations_number):
                    if ((1<<b) & B) > 0:
                        rel_num = self.union(rel_num, self.compose((1<<a), (1<<b)))
        return rel_num

    def compose_calculate_alternative_1(self, A, B):
        A = self.relations_num_to_text[A].split(" ")
        B = self.relations_num_to_text[B].split(" ")
        rel_num = 0
        for a in A:
            a = self.relations_text_to_num[a]
            for b in B:
                b = self.relations_text_to_num[b]
                rel_num = self.union(rel_num, self.compose(a, b))
        return rel_num


    def converse(self, A):
        return self.converse_table[A]

    def union(self, A, B):
        return A | B

    def intersect(self, A, B):
        return A & B

    def complement(self, A):
        return ~A

class application:
    vtimed = True
    vdebug = False
    vallow_reading_existing = True
    calculus = None
    calculus_path = None
    qcsp = None
    qcsp_path = None
    solver = None

    def __init__(self):
        self.main()

    def main(self):
        while True:
            self.eval(input())

    def eval(self, cmd):
        cmds = cmd.split(" ")
        match(cmds[0]):
            case "exit" | "e":
                exit()
            case "timed" | "t":
                self.vtimed = not self.vtimed
                print("timed:", self.vtimed)
            case "read" | "r":
                self.vallow_reading_existing = not self.vallow_reading_existing
                print("read prev files:", self.vallow_reading_existing)
            case "debug" | "d":
                self.vdebug = not self.vdebug
                print("debug printout:", self.vdebug)
            case "calculus" | "c":
                self.calculus_path = "calculi/" + cmds[1] + "/" + cmds[1]
                try:
                    self.calculus = calculus(self.calculus_path, debug=self.vdebug, timed=self.vtimed, allow_reading_existing=self.vallow_reading_existing)
                    print("Calculus loaded")
                except:
                    print("Unknown calculus")
            case "qcsp" | "q":
                self.qcsp_path = self.calculus_path[:self.calculus_path.rfind("/")] + "/qcsps/" + cmds[1] + ".csp"
                print("trying to load:", self.qcsp_path)
                #try:
                self.qcsp = qcsp(self.qcsp_path, self.calculus, debug=self.vdebug, timed=self.vtimed, allow_reading_existing=self.vallow_reading_existing)
                print("CCSP loaded")
                #except:
                #    print("Unknown qcsp for the given calculus")
            case "solve" | "s":
                self.solver = solver(self.qcsp)
                print(self.solver.refinement_search_1(deepcopy(self.solver.qcsp.qcsp_table)))
                print("dong")
            case "print" | "p":
                self.solver.qcsp.print_qcsp()
            case _:
                print("Unknown command: ", cmds[0])

a = application()