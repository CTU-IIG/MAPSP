/**********************************************************************
 * Multi-Agent Project Scheduling Problem - An exact approach
 *
 * Author:  Premysl Sucha, Cyril Briand and Ngueveu Sandra Ulrich, (C) 2011
 *
 *          CNRS, LAAS, 7 avenue du colonel Roche, F-31077 Toulouse Cedex 4, France
 *           and
 *          Czech Technical University in Prague, Karlovo namesti 13, 121 35, Prague , Czech Republic
 *
 * Creation Date: 18.10.2011 at 20:20:12
 *
 * Purpose: This model solves the Multi-Agent Project Scheduling Problem. 
 *          The objective is to find a Nash equilibrya which minimizes the project makespan.
 *          Fore more details, please see article "Finding an optimal Nash equilibrium
 *          to the multi-agent project scheduling problem". If you find this code
 *          helpful, please cite our paper.
 *          
 **********************************************************************/

/**********************************************************************/
/* GENERAL MODEL PARAMETERS */
int searchNash = 1;					//1 - objective is to find Nash equlibria, 0 - agents must have nonnegative profit

string sharingPolicy = "fixed"; 	/*This parameter defines the default sharing policy, 
									  however it is used only if it is not defined in "param.txt"!!!
									  The feasible values are: "equal", "numberOfActivities", "crashingCost", "fixed" and "variable".*/
									  
int debugMode = 1;					//script configuration: verbosity mode  (1=verbose, 0=silent)

int tightenBounds = 0;				//run a heuristic to improve bounds of selected variables


/**********************************************************************/
/* INPUT PARAMETERS OF THE MODEL */
int NumNodes = ...;   			//number of nodes (n)
range Nodes = 1 .. NumNodes;

int NumAgents = ...;			//number of agents (m)
range Agents = 1 .. NumAgents;

float CmaxUB = ...;				//makespan upper bound (the value is computed during the model initialization)
float dailyRewardFactor = ...;	//parameter is not used any more
string userParam = ...;			//user defined parameter (not used)
float Pi = ...;					//project daily reward
float wu[u in Agents] = ...;	//daily reward sharing

// Create a record to hold information about each arc (activity)
tuple arc {
   key int fromnode;
   key int tonode;
   float cost;
   float pLB;
   float pUB;
   int agent;
}

// Get the set of arcs
{arc} Arcs = ...;

float epsilon = 1/NumNodes;		//minimal considered processing time change


/**********************************************************************/
/* INITIALIZATION SCRIPTS */

/* script "extract" pUB from array of Arcs tuples */
int pUBArray[a in Arcs];

execute copypUbToArray
{
	for(var a in Arcs)
   	{
   	  pUBArray[a] = a.pUB;
    }   	  
}


/* script determining/modifiing sharing policy w_u */
float profitSharingNumberOfActivities[u in Agents];
float profitSharingCrashingCostOfActivities[u in Agents];
float totalCrashingCost = 0;
float totalNumberOfNondummyActivities = 0;
int variableProfitSharing;						//1 - wu is variable, 0 - wu is constant

execute modifyWu
{ 
	if(userParam != "") sharingPolicy = userParam;

	for(var a in Arcs)
	{
	  if(a.agent == 1) continue;
	  profitSharingNumberOfActivities[a.agent]++;
	  totalNumberOfNondummyActivities++;
	  profitSharingCrashingCostOfActivities[a.agent] += a.cost;
	  totalCrashingCost += a.cost;
	}
	
	if(sharingPolicy != "equal" && sharingPolicy != "numberOfActivities" &&
	   sharingPolicy != "crashingCost" && sharingPolicy != "fixed" &&
	   sharingPolicy != "variable") writeln("Unknown policy!");
	
	variableProfitSharing = 0;
		  
    for(var u=2; u<=NumAgents; u++)
	{
	  if(sharingPolicy == "equal") wu[u] = 1/(NumAgents-1);
	  if(sharingPolicy == "numberOfActivities") wu[u] = profitSharingNumberOfActivities[u] / totalNumberOfNondummyActivities;
	  if(sharingPolicy == "crashingCost") wu[u] = profitSharingCrashingCostOfActivities[u] / totalCrashingCost;
	  if(sharingPolicy == "variable") variableProfitSharing = 1;
	}
} 



/* script computes the longest path in the project network, i.e. trivial makespan upper bound */
int longestPath[Nodes][Nodes];
int maximalProjectDuration;

execute computeCmaxUB
{   
	var indexI;
	var indexJ;
	var indexK;
	for(indexI=1; indexI<=NumNodes; indexI++)
	{
		for(indexJ=1; indexJ<=NumNodes; indexJ++)  
			longestPath[indexI][indexJ] = -1;
			
		longestPath[indexI][indexI] = 0;	
	}	  
	
	for(var a in Arcs)
	{
	  longestPath[a.fromnode][a.tonode] = a.pUB;
	}		  
  
  
	for(indexK=1; indexK<=NumNodes; indexK++)
		for(indexI=1; indexI<=NumNodes; indexI++)
			for(indexJ=1; indexJ<=NumNodes; indexJ++)
			{
			  if(longestPath[indexI][indexK] == -1 || longestPath[indexK][indexJ] == -1 || indexI == indexJ) continue;
			  
			  if(longestPath[indexI][indexJ] <  longestPath[indexI][indexK] + longestPath[indexK][indexJ])
			  	longestPath[indexI][indexJ] =  longestPath[indexI][indexK] + longestPath[indexK][indexJ]
	  		}
	
	if(CmaxUB > longestPath[1][NumNodes]) CmaxUB = longestPath[1][NumNodes];	
	maximalProjectDuration = longestPath[1][NumNodes];
}

/* script computes sum of crashing costs over all activities - used as big M is some constraints */
float maxMaxCutCost;
execute computeMaxArcCost
{
  maxMaxCutCost = 1;
  for(var a in Arcs)
  {
     maxMaxCutCost += a.cost;
  }
}

float M = maxMaxCutCost;

/* script computes maximal total crashing price for all activities - used for poor strategy elimination */
float maxTotalCrashingCost;
execute computeMaxTotalCrashingCost
{
    maxTotalCrashingCost = 1;		//this "constant" is about 1 higher due to constraint in the ILP model
    for(var a in Arcs)
	{
	  maxTotalCrashingCost += a.cost * (a.pUB - a.pLB);
	}
}



/**********************************************************************/
/* DECISION VARIABLES OF THE MODEL */
dvar int+ p[a in Arcs];

dvar float+ s[a in Arcs] in 0 .. CmaxUB;

dvar float+ t[Nodes] in 0 .. CmaxUB;

dvar int critical[a in Arcs] in 0 .. 1;				//z_{ij}
dvar int critForward[a in Arcs] in 0 .. 1;			//x_{ij}
dvar int critBackward[a in Arcs] in 0 .. 1;			//y_{ij}

dvar float+ forwardCost[u in Agents, a in Arcs] in 0 .. a.cost;	//\underline{c}_{ij}^u
dvar float+ backwardCost[u in Agents, a in Arcs];				//\overline{c}_{ij}^u

dvar int+ alpha[u in Agents, a in Arcs] in 0 .. 1;
dvar int+ beta[u in Agents, a in Arcs] in 0 .. 1;
dvar int+ gama[u in Agents, i in Nodes] in 0 .. 1;

dvar float+ flow[u in Agents, a in Arcs];

dvar float+ ac[u in Agents, a in Arcs];				//\underline{c}_{ij}^u * \alpha_{ij}^u
dvar float+ bc[u in Agents, a in Arcs];				//\overline{c}_{ij}^u * \beta_{ij}^u

dvar float+ minFlow[u in Agents] in 0 .. Pi;
dvar float+ maxCutCost[u in Agents] in 0 .. Pi;

float profit[u in Agents];

dexpr float Cmax = t[NumNodes] - t[1];				//project makespan
						 
dexpr float agentCrashingCost = sum(<i,j,cost,pLB,pUB,agent> in Arcs : cost > 0) (cost * (pUB - p[<i,j,cost,pLB,pUB,agent>]));

dvar float+ wuVar[u in Agents] in 0 .. 1;
dvar float+ wuVarSubst[u in Agents] in 0 .. CmaxUB;
float resultingWu[u in Agents];



/**********************************************************************/
/* THE ILP MODEL */

minimize Cmax + agentCrashingCost / maxTotalCrashingCost;

subject to 
{  
	CMAXBOUND:
	  Cmax <= CmaxUB;
	  
	AUXILIARYBOUND:
	  agentCrashingCost <= maxTotalCrashingCost - 1;

   	// Preserve precedence constraints
   	forall (a in Arcs)
   	{
   	    PROCTIMEBOUND1:
   	    p[a] >= ceil(a.pLB);
   	    PROCTIMEBOUND2:
   	    p[a] <= floor(a.pUB);
   	    
   	    PREC:
		t[a.fromnode] + p[a] + s[a] - t[a.tonode] == 0;
    }		

	if(searchNash == 1)
	{	
			
	   	forall (a in Arcs)
	   	  {
	   	    CRITICAL1:
	   	    epsilon - critical[a] <= s[a];
	   	    CRITICAL2:
	   	    s[a] <= (1 - critical[a])*CmaxUB;
	      }   	  		
	
	   	forall (a in Arcs)
	   	  {
	   	      if(a.fromnode >= 2 )
	   	      {
	   	       CRITICAL_PATH1:
	   	       critical[a] <= sum(<i,a.fromnode,cost,pLB,pUB,agent> in Arcs) critical[<i,a.fromnode,cost,pLB,pUB,agent>];
	          }   	    
	   	      if(a.tonode <= NumNodes - 1 )
	   	      {
	   	        CRITICAL_PATH2:
	   	        critical[a] <= sum(<a.tonode,i,cost,pLB,pUB,agent> in Arcs) critical[<a.tonode,i,cost,pLB,pUB,agent>];
	          }
	      } 
			
	   	//Determine whether the arc can be considered in the max cut as forward arc
	   	forall (a in Arcs)
	   	  {	
	   	    CRITFORWARD1:
	   	    critForward[a] <= a.pUB - p[a];
	   	    CRITFORWARD2:
	   	    a.pUB - p[a] <= critForward[a]*(a.pUB - a.pLB);
	   	    CRITFORWARD3:
	   	    critical[a] >= critForward[a];
	      }   		
	   		
	   	//Determine whether the arc can be considered in the max cut as backward arc
	   	forall (a in Arcs)
	   	  {	
	   	    CRITBACKWARD1:
	   	    critBackward[a] <= p[a] - a.pLB;
	   	    CRITBACKWARD2:
	   	    p[a] - a.pLB <= critBackward[a]*(a.pUB - a.pLB);
	   	  }   
	   
	    /* Transformation of x_ij and y_ij onto max-cut problem .*/
	   	forall (u in Agents, a in Arcs)
	   	  {		
	   	    MAXCUTCOST:
	   	    if(a.agent == u)
	   	    {
	   	      forwardCost[u,a] == a.cost - (1-critForward[a])*a.cost;
	   	      backwardCost[u,a] == a.cost + (1 - critBackward[a])*M - (1 - critical[a])*a.cost;
	        }
	        else
	        {
	          forwardCost[u,a] == 0;
	          backwardCost[u,a] == M * critical[a];
	        }             	      
	      }   
	    
	    /* Max-cut problem formulation. */
	    forall (u in Agents, a in Arcs)
	      {
	        MAXCUT1:
	        alpha[u,a] - beta[u,a] - gama[u,a.fromnode] + gama[u,a.tonode] <= 0;
	      }    
	    
	    forall (u in Agents)
	      {  
	        MAXCUT2:
	    	gama[u,1] == 1;
	    	gama[u,NumNodes] == 0;
	  	  }
	  	  
	  	/* Min-flow problem formulation. */  
	  	forall (u in Agents, i in Nodes)
	  	  {
	  	      if(i > 1 && i < NumNodes)
	  	      {
	  	        MINFLOW:
	  	        sum (<fromnode,i,cost,pLB,pUB,agent> in Arcs) flow[u,<fromnode,i,cost,pLB,pUB,agent>]
	  	    	   == sum (<i,tonode,cost,pLB,pUB,agent> in Arcs) flow[u,<i,tonode,cost,pLB,pUB,agent>];
	          }  	    	
	      }
	        	    
	  	forall (u in Agents, a in Arcs)
	  	  {  	
	  	    MINFLOWBOUND_LOW:    	
	  	    forwardCost[u,a] <= flow[u,a];
	  	    MINFLOWBOUND_HIGH:
	  	    flow[u,a] <= backwardCost[u,a];
	      }  
	      
	    /* ac_ij^u = c_ij^u * alpha_ij^u and bc_ij^u = c_ij^u * beta_ij^u */  	    
	  	forall (u in Agents, a in Arcs)   
	  	{
	  	  CTIMESALPHA1:
	  	  ac[u,a] <= alpha[u,a]*a.cost;
	  	  CTIMESALPHA2:
	  	  ac[u,a] <= forwardCost[u,a];
	  	  CTIMESALPHA3:
	  	  ac[u,a] >= forwardCost[u,a] - (1-alpha[u,a])*a.cost;
	
		  CTIMESBETA1:
	  	  bc[u,a] <= beta[u,a]*M*3;
	  	  CTIMESBETA2:
	  	  bc[u,a] <= backwardCost[u,a];
	  	  CTIMESBETA3:
	  	  bc[u,a] >= backwardCost[u,a] - (1-beta[u,a])*M*3;
	    }
	    
	    /* force Max-Cut cost to be equal to the Min Flow */  
	    forall (u in Agents)
	      {
	        DUALSUBPROB:
	        minFlow[u] == sum (<1,i,cost,pLB,pUB,agent> in Arcs) flow[u,<1,i,cost,pLB,pUB,agent>];
	        PRIMALSUBPROB:
	        maxCutCost[u] == sum (<fromnode,tonode,cost,pLB,pUB,agent> in Arcs) ac[u,<fromnode,tonode,cost,pLB,pUB,agent>]
	        - sum (<fromnode,tonode,cost,pLB,pUB,agent> in Arcs) bc[u,<fromnode,tonode,cost,pLB,pUB,agent>];
	        
	        PRIMALDUAL:
	        minFlow[u] <= maxCutCost[u];
	      }       
	    
	    /* Limit cost of Max-Cut, i.e. profit of each agent. */  	 
	    forall (u in Agents)
	      {
	        PROFIT:
	        maxCutCost[u] <= Pi*wuVar[u] + 0.0000001; //+ 0.00000001;
	      }
	
	}
	else
	{
	    if(variableProfitSharing == 1)
	    {
		    forall (u in Agents)
		      {
		        POSITIVE_PROFIT:
		  			0 <= Pi*wuVarSubst[u] - sum(a in Arcs : a.agent == u) (a.cost*(a.pUB - p[a]));
			  }
	    }      
	    else
	    {
		    forall (u in Agents)
		      {
		        POSITIVE_PROFIT2:
		  			0 <= Pi*wuVar[u]*(maximalProjectDuration - (t[NumNodes] - t[1])) - sum(a in Arcs : a.agent == u) (a.cost*(a.pUB - p[a]));
			  }
	    }	    		
	}

    forall (u in Agents)
    {
        PROFIT_SHARING:
        if(variableProfitSharing == 0)
        {  
         	CONSTANTSHARING:
        	wuVar[u] == wu[u];
        	
        	forall (u in Agents)
        	{
        	  	wuVarSubst[u] == 0;			//This wariable is not used in this case
           	}        	    
        }
        else
        {   
        	if(searchNash == 1)
        	{
        	  	TOTALREWARD100PERCENT_NASH:
		    	sum(u in Agents : u > 1) (wuVar[u]) == 1;   
		    	wuVar[1] == 0;        	  
         	}
         	else
         	{        	  
	        	TOTALREWARD100PERCENT_NONASH:     
		    	sum(u in Agents : u > 1) (wuVarSubst[u]) == (maximalProjectDuration - (t[NumNodes] - t[1]));   
		    	wuVarSubst[1] == 0;
    		}	    	
   		}	             
    }

      
}

/* method copyes results from a decision variable to an ordinary variable */
float SolutionP[a in Arcs];		//output variable (dvar cannot be passed into another ILP model)
execute CopyResults {
  for(var a in Arcs)
  {
     SolutionP[a] = p[a];
  }
  
  for(u in Agents)
  {
    if(variableProfitSharing == 1 && searchNash == 0)
    {
  		resultingWu[u] = wuVarSubst[u] / (maximalProjectDuration - (t[NumNodes] - t[1]));
 	}
 	else
 	{
 	  	resultingWu[u] = wuVar[u];
  	} 	    	
  }
    
  for(var u in Agents)
  {
    profit[u] = Pi*resultingWu[u]*(maximalProjectDuration - (t[NumNodes] - t[1]));
    for(a in Arcs)
    {
      	if(a.agent == u) profit[u] -= a.cost*(a.pUB - p[a]);
 	}  	
  } 	
}




/*************************************************************************/
/* MAIN */
/*************************************************************************/
/* auxiliary function */
execute
{
    function isNearEqual(result, expectedResult)
  	{
    	var tolerance = 0.0001;
  		return Math.abs(expectedResult-result)<tolerance;
  	}
}  

/*************************************************************************/
/* main control script - solves the model and tests the Nash equilibrium */
main
{   	
   	var instanceSolution = "";			//auxiliary variable
  
   	var NashEquilibrium;					//function return value
   	NashEquilibrium  = 1;

   
   	/**********************************************************************/
   	/* Read user parameters */
	var dailyRewardFactor;
	var sharingPolicy;
	var paramFileHandler = new IloOplInputFile("param.txt");
   	dailyRewardFactor = paramFileHandler.readline();
   	sharingPolicy = paramFileHandler.readline();
   	paramFileHandler.close();   
   
   
   	/**********************************************************************/
   	/* Create the master-model */
   	var masterDef = thisOplModel.modelDefinition;
   	var masterCplex = cplex;
   	var masterData = thisOplModel.dataElements;
   	
	var masterOpl = new IloOplModel(masterDef,masterCplex);
	var modifiedPi = masterData.Pi * dailyRewardFactor;
	masterData.Pi = modifiedPi;
	masterData.CmaxUB = 10000000000;
	masterData.userParam = sharingPolicy;
  	masterOpl.addDataSource(masterData);
    masterOpl.generate();
      
	if(masterOpl.debugMode == 1) writeln("makespan bound: ", masterOpl.maximalProjectDuration);
	instanceSolution += "normal makespan = " + masterOpl.maximalProjectDuration + ", ";
	
   	/*****************************************************************************/
   	/*---- Sub model - Determines makespan bound with respect to Nash equilibria ----*/ 
   	var CmaxBound = masterOpl.maximalProjectDuration;
   	
   	if(masterOpl.searchNash == 1 && masterOpl.tightenBounds == 1)
   	{	   	
	    var subBoundSource;
	    var subBoundDef;
	    var subBoundCplex;    
	    var subBoundOpl;    
	   	var subBoundData;
	
	    subBoundSource = new IloOplModelSource("oneAgent.mod");
	    subBoundDef = new IloOplModelDefinition(subBoundSource);
	    subBoundCplex = new IloCplex();        
	
	   	var previousStrategy = masterOpl.pUBArray;
	   	
	   	for (var u1=2; u1 <= masterOpl.NumAgents; u1++)
	   	{
		   for (var v=1; v < u1; v++)
		   {
	     
			    // Ceating the sub model	
			    subBoundOpl = new IloOplModel(subBoundDef,subBoundCplex);	   
			   	subBoundData = new IloOplDataElements();
			   	
			   	subBoundData.NumNodes = masterOpl.NumNodes;
			   	subBoundData.NumAgents = masterOpl.NumAgents;
			   	subBoundData.CmaxUB = masterOpl.maximalProjectDuration;
			   	subBoundData.Pi = masterOpl.Pi;
			   	subBoundData.wu = masterOpl.wu;
			   	subBoundData.Arcs = masterOpl.Arcs;
			   	subBoundData.agentsWithHigherOrEqualIndexHasPEqualPUB = u1 + 1;
			   	if(v == 1) subBoundData.curentAgent = u1;
			   	else subBoundData.curentAgent = v;
			   	subBoundData.SolutionP = previousStrategy;
			   	subBoundOpl.addDataSource(subBoundData); 
			   	subBoundOpl.generate();
			   	
			   	if(subBoundCplex.solve())
			   	{
			   	    if(masterOpl.debugMode == 1)
			   	    {
				   	  	writeln(" makespan=",subBoundOpl.t[masterOpl.NumNodes] - subBoundOpl.t[1]);
		       		}	   	      	
			    } 
			    else
			    {
			      writeln("NOT FEASIBLE SOLUTION!");
			      NashEquilibrium = 0;
			    }      
			    
			    subBoundOpl.postProcess();
			    previousStrategy = subBoundOpl.SolutionOutput;
			    CmaxBound = subBoundOpl.t[masterOpl.NumNodes] - subBoundOpl.t[1];
			    
			    subBoundData.end();
			    //subBoundOpl.end();
	  		}   
	   	}	
				
	    subBoundCplex.end();
	    subBoundDef.end();
	    subBoundSource.end();

		//create improved master model
		masterData.end();
	   	masterOpl.end();
		masterOpl = new IloOplModel(masterDef,masterCplex);
		masterData = thisOplModel.dataElements;
		masterData.Pi = modifiedPi;
	   	masterData.CmaxUB = CmaxBound;   
		masterData.userParam = sharingPolicy;
	  	masterOpl.addDataSource(masterData);
	    masterOpl.generate();   
	    
   		if(masterOpl.debugMode == 1) writeln("Improved makespan bound: ", CmaxBound);
   		instanceSolution += CmaxBound + " ";
	}	



   	/**********************************************************************/
   	/* Execute the master-model */

   	//solve the master-model
   	var startTime = new Date();
   	if(!cplex.solve())
   	{
     	writeln("Infeasible instance!");
     	NashEquilibrium = 0;
     	NashEquilibrium;
   	}   
   	var stopTime = new Date();
   	var CPUTime = (stopTime - startTime) / 1000.0;
   
   	masterOpl.postProcess();
   	var Cmax = masterOpl.t[masterOpl.NumNodes] - masterOpl.t[1];

   	//display results according to the mode
   	if(masterOpl.debugMode == 1)
   	{
	   writeln("Main model (makespan)", Cmax);
	   writeln("Main model (max-cut)", masterOpl.maxCutCost);
	   writeln("Main model (min-flow)", masterOpl.minFlow);
	   writeln("Main model (profit)", masterOpl.profit);
	   writeln("Main model (t)  ", masterOpl.t);
	   writeln("Main model (p)  ", masterOpl.p);
	   writeln("Main model (s)  ", masterOpl.s);
	   writeln("Main model (z)  ", masterOpl.critical);	   
	   writeln("Main model (forwardCost)  ", masterOpl.forwardCost);	
	   writeln("Main model (backwardCost)  ", masterOpl.backwardCost);	
	   writeln("Main model (wuVar)  ", masterOpl.wuVar);	
	   
	      
	   writeln("CPU time: ", CPUTime);
	   writeln("nodes: " + cplex.getNnodes());
	   writeln("iterations: " + cplex.getNiterations());
   	}
   	else
   	{
     	instanceSolution += "makespan = " + Cmax + ", CPUTime = " + CPUTime;
//     	instanceSolution += Cmax + " " + CPUTime + " " + cplex.getNnodes() + " " + cplex.getNiterations() + " " + cplex.getNrows() + " " + cplex.getNcols();
   	}        
   
   
   
   
   	/**********************************************************************/
   	/*---- Sub model - tests whether a single agent can make a profit ----*/ 
   	for (var u=1; u <= masterOpl.NumAgents && NashEquilibrium == 1 && masterOpl.searchNash == 1; u++)
   	{
	    // Ceating the sub model
	    var subSource = new IloOplModelSource("oneAgent.mod");
	    var subDef = new IloOplModelDefinition(subSource);
	    var subCplex = new IloCplex();    
	    
	    var subOpl = new IloOplModel(subDef,subCplex);    
	   
	   	var subData = new IloOplDataElements();
	   	subData.NumNodes = masterOpl.NumNodes;
	   	subData.NumAgents = masterOpl.NumAgents;
	   	subData.CmaxUB = masterOpl.maximalProjectDuration;
	   	subData.Pi = masterOpl.Pi;
	   	subData.wu = masterOpl.resultingWu;
	   	subData.Arcs = masterOpl.Arcs;
	   	subData.agentsWithHigherOrEqualIndexHasPEqualPUB = masterOpl.NumAgents + 1;
	   	subData.curentAgent = u;
	   	subData.SolutionP = masterOpl.SolutionP;
	   	subOpl.addDataSource(subData); 
	   	subOpl.generate();
	   	   
	   	if(subCplex.solve())
	   	{
	   	    if(masterOpl.debugMode == 1)
	   	    {
		   	  	writeln("SUB OBJECTIVE: ",subCplex.getObjValue(),
		   	  		  ", makespan=",subOpl.t[masterOpl.NumNodes] - subOpl.t[1]);
		   	    //writeln(subOpl.p);
       		}
       			   	          
	   	    if(!isNearEqual(masterOpl.profit[u], subCplex.getObjValue()))
	   	    {
	   	      	writeln(masterOpl.profit[u]);
	   	      	writeln(subCplex.getObjValue());
	   	      	NashEquilibrium = 0;
	   	      	writeln("An incorrect result!");
          	}	   	      	
	    } 
	    else
	    {
	      writeln("NOT FEASIBLE SOLUTION!");
	      NashEquilibrium = 0;
	    }        	
	   	subData.end();
	   	subOpl.end();
	
	    subCplex.end();
	    subDef.end();
	    subSource.end();
  	}   

	if(NashEquilibrium == 1)
	{
	  	writeln(instanceSolution);
 	}
 	else
 	{
 	  	writeln("Incorrect result!!!");
  	} 	  	  

	NashEquilibrium;
} 


