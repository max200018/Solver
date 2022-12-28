from copy import deepcopy
from fractions import Fraction
from heapq import heapify, heappop
incremental_nVars = 50

class cdcl_solver_s(object):
    def __init__(self, file = None, nVars = incremental_nVars, nClauses = 0, Clauses = None):
        self.used_nVars = 0
        self.propagate_calls = 0
        self.add_times = 0

        if(Clauses is not None):
            self.solver_init(nVars, len(Clauses))
            self._parse_formula(Clauses)
            self.used_nVars = nVars
  
        elif(file is not None):
            self.parse(file) 
        else:
            self.solver_init(nVars, nClauses)

    def solver_init(self, nVars, nClauses):
        self.nVars = nVars
        self.nClauses = nClauses
  
        self.literals = {i: Lit(i) for i in range(-nVars, nVars+1) if i != 0}
        self.var_inc = -1
        self.watchers = {i: [] for i in self.literals}
        self.clauses = []
        self.var_order = []

    def extend(self, nVars = incremental_nVars):
        if(nVars < incremental_nVars): nVars = incremental_nVars
        self.nVars += nVars
        for i in range(-self.nVars, self.nVars+1):
            if(i!=0 and not i in self.literals):
                self.literals[i] = Lit(i)
                self.watchers[i] = []

    def delete(self):
        del self

    def extend_formula(self, formula):
        for cl in formula:
            self.add_clause(cl)
    
    def propagate(self):
        if(self.propagate_calls == 0): self.restart()
        self.propagate_calls += 1
        conflict = self._propagate()
        if(conflict):
            # конфликт
            if(self.level == 0):
                return None
            else:
                self.analyze(conflict)
                self.restart()
                return []
        else:
            # конфликта нет
            return self.get_propagate_model()

    def _propagate(self):
       
        unit_literals = set()
        if(self.level == 0):
            for clause in self.clauses:
            
                if(clause.is_unit()):
                    lit = clause[0].to_int()
                 
                    unit_literals.add(lit)
                   
                    self.decisions[self.level].add(lit)
                    self.i_graph[lit] = (self.level, [])
        else:
         
            lit = next(iter(self.decisions[self.level]))
            unit_literals.add(lit)
 
        while(len(unit_literals) > 0):
       
            l = unit_literals.pop()
            if(self.literals[l].is_false()): return l
  
            self.literals[l].set_true()
            self.literals[-l].set_false()
            indexes = self.cur_watchers[l].copy()
            
            for i in indexes:
                clause = self.clauses[i]
                
                if(clause.is_satisfied()):
                  
                    continue
                
                elif(clause.is_unit()):
                   
                    unit_lit = clause.get_unset().to_int()
                    if unit_lit in self.i_graph:
                        
                        continue
                    unit_literals.add(unit_lit)
                    self.decisions[self.level].add(unit_lit)
                
                    reason = [-lit.to_int()
                            for lit in clause
                            if lit.to_int() != unit_lit]
                    self.i_graph[unit_lit] = (self.level, reason)
             
                elif(clause.is_empty()):
                    # конфликт
                    self.decisions[self.level].add(-l)
                    reason = [-lit.to_int()
                            for lit in clause
                            if lit.to_int() != -l]
                    self.i_graph[-l] = (self.level, reason)
                    
                    return l
                
                else:
                    thing = iter(clause)
                    while(True):
                        lit = next(thing)
                        
                        if(not lit.is_unset()):
                            continue
                        lit = lit.to_int()
                       
                        if(i in self.cur_watchers[-lit]):
                            continue
                       
                        self.cur_watchers[l].remove(i)
                    
                        self.cur_watchers[-lit].append(i)
                        break
        return False
    def restart(self):
       
        for lit in self.literals.values():
            lit.unset()
       
        self.cur_var_order = deepcopy(self.var_order) 
    
        self.var_order_finder = {lit: i for i, [p, lit] in enumerate(self.cur_var_order)}
        
        self.cur_watchers = deepcopy(self.watchers)
   
        self.decisions = {0: set()}
        self.i_graph = {}
       
        self.level = 0
        self.propagate_calls = 0 

    def satisfied(self):
        return all(clause.is_satisfied() for clause in self.clauses)
    def decide(self):

        heapify(self.cur_var_order)

        next_lit = 0

        for _ in range(len(self.cur_var_order)):
            lit = heappop(self.cur_var_order)[1]
            if(self.literals[lit].is_unset()):
                next_lit = lit
                break
     
        self.var_order_finder = {lit: i for i, (p, lit) in enumerate(self.cur_var_order)}

        self.level += 1
        self.decisions[self.level] = {next_lit}
        self.i_graph[next_lit] = (self.level, [])


    def analyze(self, l):
        # поиск первой уникальной точки импликации
        uips = set()
        weights = {lit: Fraction() for lit in self.decisions[self.level]}

        def explore(lit, weight):
            weights[lit] += weight
          
            next_lits = [next_lit
                        for next_lit in self.i_graph[lit][1]
                        if self.i_graph[next_lit][0]==self.level]
            
            for next_lit in next_lits:
                explore(next_lit, weight / len(next_lits))
 
        explore(l, Fraction(1.))

        for lit in weights.keys():
            if(weights[lit] == Fraction(1.)):
                uips.add(lit)
            uips.discard(l)

        lit = l    
        while(True):
            for next_lit in self.i_graph[lit][1]:
                if(self.i_graph[next_lit][0] == self.level):
                    lit = next_lit
                    break
            if(lit in uips):
                fuip = lit
                break

        new_clause = {-fuip}
        def find_cut(lit):
           
            if(self.i_graph[lit][0]!=self.level):
                new_clause.add(-lit)
                return
            
            if(lit == fuip):
                return
            
            for next_lit in self.i_graph[lit][1]:
                find_cut(next_lit)       
        find_cut(l)
        find_cut(-l)

        self._addClause(new_clause)

    def add_clause(self, clause):
        self.add_times += 1
    
        has_extend = False
        for i in clause:
            if(abs(i) > self.used_nVars):
                has_extend = True
                self.used_nVars = abs(i)
            if(abs(i) > self.nVars):
                self.extend(abs(i)-self.nVars)

        if(not has_extend):
            self._addClause(clause)
            return

        self.clauses.append(Clause([self.literals[lit] for lit in clause]))
        clause_idx = len(self.clauses)-1
        clause_iter = iter(self.clauses[-1])

        # добавление литералов
        for _ in range(min(2, len(clause))):
            lit = next(clause_iter)
            self.watchers[-lit.to_int()].append(clause_idx)

        heap_dict = {i: 1. for i in clause}
        for lit in clause:
            heap_dict[lit] += self.var_inc
        for i in heap_dict:
            if(i in self.var_order_finder):
                idx = self.var_order_finder[i]
                self.var_order[idx][0] += heap_dict[i]
            else:
                self.var_order_finder[i] = len(self.var_order)  
                self.var_order.append([heap_dict[i], i])

    def _addClause(self, clause):
        
        self.clauses.append(Clause([self.literals[lit] for lit in clause]))
        clause_idx = len(self.clauses)-1
        clause_iter = iter(clause)
        
        for _ in range(min(2, len(clause))):
            lit = next(clause_iter)
            self.watchers[-lit].append(clause_idx)
        self.var_inc*= 1 / .95
       
        for lit in clause:
            if(lit not in self.var_order_finder):
                continue

            var_order_item = self.cur_var_order[self.var_order_finder[lit]]
            var_order_item[0] += self.var_inc

            if(var_order_item[0]>1e100):
                self.var_inc *= 1e-100

                for item in self.cur_var_order:
                    item[0] *= 1e-100

    
    def solve(self) -> bool:
        while(True):           
            conflict = self._propagate()
            
            if(conflict):
               
                if(self.level==0):
                    return False
                else:
                    
                    self.analyze(conflict)
                  
                    self.restart()
            
            else:
                if(self.satisfied()):
                    return True
                else:
                  
                    self.decide()

    def get_propagate_model(self):
        model = []
        for i in range(2, self.used_nVars+1):
            if(not self.literals[i].is_unset()):
                if(self.literals[i].is_false()):
                    model.append(-i)
                else:
                    model.append(i)
        return model

    def get_model(self):
        model = [l for l in self.i_graph]
        self.model = []
        self.model.extend([-l if -l in model else l
                        for l in range(1, self.used_nVars+1)])
        return self.model

    def _parse_formula(self, clauses):
        for clause in clauses:
            self.clauses.append(Clause(list({self.literals[int(x)]
                                        for x in clause})))
        heap_dict = {i: 1. for i in self.literals}
        for i, clause in enumerate(self.clauses):
            for lit in clause:
                heap_dict[lit.to_int()] += self.var_inc
            for j in range(min(2, len(clause))):
                lit = clause[j]
                self.watchers[-lit.to_int()].append(i)
        self.var_order = [[p, lit] for lit, p in heap_dict.items()]
        self.restart()

    def parse(self, file):
        f = open(file, 'r')
        lines = f.readlines()
        f.close()
        lines = [line for line in lines if line[0]!='c' or line[0]!='\n']
        index = 0
     
        params = lines[0].split()
        if(len(params)!=0 and params[0]=='p' and params[1]=='cnf'):
      
            self.solver_init(int(params[2]), int(params[3]))
         
            self.used_nVars = int(params[2])
            index += 1

        nZeros = int(self.nClauses)
        while(nZeros>0):
            clause = [int(x) for x in lines[index].split()]
            clause = clause[:-1]
            self.clauses.append(Clause(list({self.literals[int(x)] for x in clause})))
            nZeros -= 1
            index += 1
        heap_dict = {i: 1. for i in self.literals}
        for i, clause in enumerate(self.clauses):
            for lit in clause:

                heap_dict[lit.to_int()] += self.var_inc
            for j in range(min(2, len(clause))):
                lit = clause[j]
                self.watchers[-lit.to_int()].append(i)
        self.var_order = [[p, lit] for lit, p in heap_dict.items()]
        self.restart()


class Clause:
    def __init__(self, lits):
        self.lits = lits

    def __getitem__(self, key):
        return self.lits[key]

    def __len__(self):
        return len(self.lits)

    def is_unit(self):
        return sum(lit.is_unset() for lit in self.lits) == 1

    def __iter__(self):
        yield from self.lits

    def is_satisfied(self):
        return any(lit.is_true() for lit in self.lits)
 
    def is_empty(self):
        return all(lit.is_false() for lit in self.lits)

    def get_unset(self):
        for lit in self.lits:
            if lit.is_unset():
                return lit

    def __str__(self):
        ans = ""
        for i in self.lits:
            ans += str(i) + " "
        
        return ans[:-1]

class Lit:

    def __init__(self, lit):
        self.lit = lit
        self.value = 0

    def set_true(self):
        self.value = 1

    def set_false(self):
        self.value = -1

    def unset(self):
        self.value = 0

    def is_true(self):
        return self.value == 1

    def is_false(self):
        return self.value == -1

    def is_unset(self):
        return self.value == 0

    def to_int(self):
        return self.lit

    def __str__(self):
        return str(self.lit)



if(__name__=="__main__"):
    s = cdcl_solver_s(file="./test.txt")

    f = s.solve()
    if f:
        print("SAT")
    else: print("UNSAT")
    if(f):
        print(s.get_model())
