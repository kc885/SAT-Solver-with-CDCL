#include <fstream>
#include <iostream>
#include <sstream>
#include <algorithm>
#include <string>
#include <vector>
#include <unordered_map>
#include <unordered_set>
#include <stdio.h>

namespace ck_cdcl_solver{
    class Solver {
    public:
        void parse(std::string filename){
            std::string line;
            std::ifstream ifs(filename);
            int clause_num = 0;
            while (ifs) {
                getline(ifs, line);
                
                //effective clause number
                int temp;
                
                if (line.size() > 0) {
                    if (line[0] == 'p') {
                        sscanf(line.c_str(), "p cnf %d %d", &variableNumber, &temp);
                        
                        //initialization
                        unsat = 0;
                        decisionVar.push_back(0);
                        for (int i =0;i <variableNumber;i++){
                            //undefined
                            val_decisionLevel.push_back(0);
                            decisionVar.push_back(0);
                            //antecedent.push_back(-1);
                            std::vector<int> temp1;
                            std::vector<int> temp2;
                            varToClause[i+1] = temp1;
                            varToClause[-i-1] = temp2;
                        }
                        val_decisionLevel.push_back(0);
                        decisionVar.push_back(0);
                        
                    } else if (line[0] == 'c' ){
                        continue;
                    } else {
                        //readClause(line, lits);
                        std::stringstream sin(line);
                        
                        //if a clause contain both a variable and its negation, this clause must evaluate to true so we can skip it.
                        int resolve_flag = 0;
                        
                        //counter for effective variable number in a clause
                        int count = 0;
                        
                        std::unordered_set<int> visited;
                        
                        int num;
                        while(sin >> num){
                            if(num == 0)
                                break;
                            if(visited.count(num) > 0)
                                continue;
                            else if(visited.count(-num) > 0)
                                resolve_flag = 1;
                            else{
                                visited.insert(num);
                                count++;
                                
                            }
                        }
                        if(count > 0 && resolve_flag == 0){
                            std::unordered_set<int> c;
                            
                            for(auto iter = visited.begin(); iter != visited.end(); iter++){
                                varToClause[*iter].push_back(clause_num);
                                c.insert(*iter);
                            }
                            
                            clauses.push_back(c);
                            clause_num++;
                        }
                        
                        
                    }
                }
                
            }
            for(int i =1;i <= variableNumber; i++){
                sor.push_back(i);
            }
            std::sort(sor.rbegin(),sor.rend(),[&](int i, int j)
                {return ((varToClause[i].size() + varToClause[-i].size()) < (varToClause[j].size() + varToClause[-j].size())) ;}
            );
          
            ifs.close();
        }
        
        void solve(){
            
            int decision_level = 1;
            
            std::unordered_set<int> implied;
            if(!unitPropagate(implied, decision_level)){
                unsat = 1;
                return;
            }
                
            int i = 0;
            while(i < variableNumber && val_decisionLevel[sor[i]] != 0)
                i++;
            if(i == variableNumber)
                return;
            
            
            decisionVar[2] = sor[i];
            val_decisionLevel[sor[i]] = -2;
            if(recursion(i+1,2))
                return ;
            
            decisionVar[2] = -sor[i];
            val_decisionLevel[sor[i]] = 2;
            if(recursion(i+1,2))
                return ;
            unsat = 1;
            return;
            
            
        }
        
        bool unitPropagate(std::unordered_set<int> &implied, int level){
            //visited array
            std::vector<int> visited(clauses.size(),0);
            
            std::unordered_set<int> intermediate;
            

            //unit propagation
            
            int new_imply_flag;
            do{
                new_imply_flag = 0;
                for (int i =0; i < (int)clauses.size(); i++){
                    if(visited[i] == 0){
                        
                        visited[i] = 1;
                        
                        //analyze this clause
                        int val = 0;
                        int undef_num = 0;
                        int target_var;
                        
                        for(auto iter = clauses[i].begin(); iter != clauses[i].end(); iter++){
                            if(val_decisionLevel[std::abs(*iter)] == 0){
                                undef_num++;
                                target_var = *iter;
                                if(undef_num > 1)
                                    break;
                            }
                            else if(val_decisionLevel[std::abs(*iter)] * (*iter) > 0){
                                val = 1;
                                break;
                            }
                        }
                        
                        if(val == 0 ){
                            //conflict
                            if(undef_num == 0){
                               
                                //learn a new clause
                                std::unordered_set<int> learnt_level;
                                std::unordered_set<int> learnt;
                                
                                for(auto iter = intermediate.begin(); iter!= intermediate.end();iter++){
                                    if(intermediate.count(-(*iter)) == 0){
                                        varToClause[*iter].push_back(clauses.size());
                                        learnt.insert(*iter);
                                    }
                                }

 
                                clauses.push_back(learnt);
                                
                                for(auto iter = implied.begin(); iter != implied.end(); iter++)
                                    val_decisionLevel[*iter] = 0;
                                return false;
                            }
                            //imply a new variable
                            else if(undef_num == 1){
                                new_imply_flag = 1;
                                implied.insert(std::abs(target_var));
                                
                                
                                val_decisionLevel[std::abs(target_var)] = (((target_var) > 0) - ((target_var) < 0))*level;
                                
                                //get variables which help to imply this variable(inclusing itself)
                                for(auto iter = clauses[i].begin(); iter != clauses[i].end(); iter++){
                                    intermediate.insert(*iter);
                                }
                                
                                for(auto iter = varToClause[target_var].begin();iter != varToClause[target_var].end(); iter++)
                                    visited[*iter] = 0;
                                for(auto iter = varToClause[-target_var].begin();iter != varToClause[-target_var].end(); iter++)
                                    visited[*iter] = 0;
                                break;        
                            }
                        }
                          
                    }  
                }

            }while(new_imply_flag == 1);
            return true;
        }
        
        bool recursion(int index, int level){
            std::unordered_set<int> implied;
            if(!unitPropagate(implied,level)){
                for(auto iter = implied.begin();iter != implied.end(); iter++)
                    val_decisionLevel[*iter] = 0;
                return false;
            }
                
            int i = index;
            while(i < variableNumber && val_decisionLevel[sor[i]] != 0)
                i++;
            if(i == variableNumber)
                return true;
            
            
            decisionVar[level+1] = sor[i];
            val_decisionLevel[sor[i]] = -level-1;
            if(recursion(i+1,level+1))
                return true;
            
            decisionVar[level+1] = -sor[i];
            val_decisionLevel[sor[i]] = level+1;
            if(recursion(i+1,level+1))
                return true;
            
            val_decisionLevel[sor[i]] = 0;
            for(auto iter = implied.begin();iter != implied.end(); iter++)
                val_decisionLevel[*iter] = 0;
            return false;
        }
        
        void printResult(){
            if(unsat == 1)
                std::cout<< "UNSAT" << std::endl;
            else{
                std::cout << "SAT" << std::endl;
                for (int i = 1;i <= variableNumber; i ++){
                    if(val_decisionLevel[i] < 0)
                        std::cout << -i << " ";
                    else
                        std::cout << i << " ";
                    
                }
                std::cout << std::endl;
            }
            
        }
        
        
            
        //Variable mapped to their occurence on each clause index
        std::unordered_map<int,std::vector<int>> varToClause;
        
        
    private:
        
        std::vector<std::unordered_set<int>> clauses;
       
        //0: undefine 1:true -1:false
        //multiply by decisional level
        std::vector<int> val_decisionLevel;
        
        //decision variables
        std::vector<int> decisionVar;
        
        //sorted variable based on their occurence on each clause 
        std::vector<int> sor;
        
        int variableNumber;
        int unsat;
    };
    
    
}

int main(int argc, char **argv){
    ck_cdcl_solver::Solver solver;
    if(argc == 1) {
      std::cout << "Please specify the input file." << std::endl;
    }
    std::string filename = argv[1];
    solver.parse(filename);  // parse input file
    solver.solve();
    solver.printResult();  // print answer
}
