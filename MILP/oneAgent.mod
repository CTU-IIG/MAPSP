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
 * Purpose: auxiliary script
 *          
 **********************************************************************/

int NumNodes = ...;   // Number of nodes
range Nodes = 1 .. NumNodes;

int NumAgents = ...;
range Agents = 1 .. NumAgents;

int curentAgent = ...;
int agentsWithHigherOrEqualIndexHasPEqualPUB = ...;

float CmaxUB = ...;		//Cmax upper bound
float Pi = ...;
float wu[u in Agents] = ...;

// Create a record to hold information about each arc
tuple arc {
   key int fromnode;
   key int tonode;
   float cost;
   float pLB;
   float pUB;
   int agent;
}

{arc} Arcs = ...;

float SolutionP[a in Arcs] = ...;
float SolutionOutput[a in Arcs];

// The MAPSP model has decision variables indexed on the arcs.
dvar float+ p[a in Arcs]; // in a.pLB .. a.pUB;

dvar float+ t[Nodes] in 0 .. CmaxUB; 

dvar float Z[Agents];

//maximize agent's profit
maximize Z[curentAgent];

subject to 
{
    t[1] == 0;
    	
	// Preserve precedence constraints
	forall (a in Arcs)
	  {
   	    PROCTIMEBOUND1:
   	    p[a] >= ceil(a.pLB);
   	    PROCTIMEBOUND2:
   	    p[a] <= floor(a.pUB);	    
	    
	    PRECEDENCE:
		t[a.fromnode] + p[a] <= t[a.tonode];
      }		
		
	  forall (a in Arcs : a.agent >= agentsWithHigherOrEqualIndexHasPEqualPUB)
	  {	
  			BOUNDS1:
    		p[a] == a.pUB;
      }
            
	  forall (a in Arcs : a.agent != curentAgent && a.agent < agentsWithHigherOrEqualIndexHasPEqualPUB)
      {    	
  			BOUNDS2:
    		p[a] == SolutionP[a];
      }
      
      forall(u in Agents)
      {
        	COSTEVALUATION:
        	Z[u] == Pi*wu[u]*(CmaxUB - (t[NumNodes] - t[1])) - sum(a in Arcs : a.agent == u) (a.cost*(a.pUB - p[a]));
      }        	
      
}  

execute DISPLAY_RESULT {
   	for(var a in Arcs)
   	{
     	settings.skipWarnNeverUsedElements = true;
      	//writeln("<",a.fromnode,",",a.tonode,",",SolutionP[a],">");
      	SolutionOutput[a] = p[a];
   	}      
} 
    
