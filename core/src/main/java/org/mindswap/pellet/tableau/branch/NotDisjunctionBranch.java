package org.mindswap.pellet.tableau.branch;

import java.util.HashSet;
import java.util.Set;
import java.util.logging.Level;

import org.mindswap.pellet.ABox;
import org.mindswap.pellet.Clash;
import org.mindswap.pellet.DependencySet;
import org.mindswap.pellet.Individual;
import org.mindswap.pellet.Node;
import org.mindswap.pellet.PelletOptions;
import org.mindswap.pellet.exceptions.InternalReasonerException;
import org.mindswap.pellet.tableau.completion.CompletionStrategy;
import org.mindswap.pellet.utils.ATermUtils;

import aterm.ATermAppl;

public class NotDisjunctionBranch extends Branch {
	protected Node node;
	protected ATermAppl disjunction;
	private ATermAppl[][] notDisj;
	protected DependencySet[] prevDS;
	protected int[] order;
	
	public NotDisjunctionBranch(ABox abox, CompletionStrategy completion, Node node, ATermAppl disjunction, DependencySet ds, ATermAppl[][] notDisj) {
		super(abox, completion, ds, notDisj.length);
		
		this.node = node;
		this.disjunction = disjunction;
		this.setDisj( notDisj );
        this.prevDS = new DependencySet[notDisj.length];
		this.order = new int[notDisj.length];
        for(int i = 0; i < notDisj.length; i++)
            order[i] = i;
	}
	
	public Node getNode() {
		return node;
	}
    
    protected String getDebugMsg() {
        return "DISJ: Branch (" + getBranch() + ") try (" + (getTryNext() + 1) + "/" + getTryCount()
            + ") Node: " + node + " Concept: " +  ATermUtils.toString( notDisj[getTryNext()][0] ) + " , " +  ATermUtils.toString( notDisj[getTryNext()][1] ) + " OF " + ATermUtils.toString(disjunction);
    }
    
	public NotDisjunctionBranch copyTo(ABox abox) {
	    Node n = abox.getNode(node.getName());
	    NotDisjunctionBranch b = new NotDisjunctionBranch(abox, null, n, disjunction, getTermDepends(), notDisj);
	    b.setAnonCount( anonCount );
	    b.setNodeCount( nodeCount );
	    b.setBranch( branch );
	    b.setStrategy( strategy );
        b.setTryNext( tryNext );

        b.prevDS = new DependencySet[notDisj.length];
        System.arraycopy(prevDS, 0, b.prevDS, 0, notDisj.length );
        b.order = new int[notDisj.length];
        System.arraycopy(order, 0, b.order, 0, notDisj.length );

	    return b;
	}
	
	/**
	 * This function finds preferred disjuncts using different heuristics.
	 * 
	 * 1) A common kind of axiom that exist in a lot of  ontologies is 
	 * in the form A = and(B, some(p, C)) which is absorbed into an
	 * axiom like sub(B, or(A, all(p, not(C))). For these disjunctions,
	 * we always prefer picking all(p, C) because it causes an immediate 
	 * clash for the instances of A so there is no overhead. For 
	 * non-instances of A, this builds better pseudo models     
     * 
	 * @return
	 */
//	private int preferredDisjunct() {
//        if( disj.length != 2 ) 
//            return -1;
//        
//        if( ATermUtils.isPrimitive( disj[0] ) && 
//            ATermUtils.isAllValues( disj[1] ) &&
//            ATermUtils.isNot( (ATermAppl) disj[1].getArgument( 1 ) ) )
//            return 1;
//            	                
//        if( ATermUtils.isPrimitive( disj[1] ) && 
//            ATermUtils.isAllValues( disj[0] ) &&
//            ATermUtils.isNot( (ATermAppl) disj[0].getArgument( 1 ) ) )
//            return 0;
//        
//        return -1;
//	}
	
    public void setLastClash( DependencySet ds ) {
    		super.setLastClash( ds );
    		if(getTryNext()>=0)
    			prevDS[getTryNext()] = ds;
    }
    
	protected void tryBranch() {			
		abox.incrementBranch();
		
		int[] stats = null;
//		if( PelletOptions.USE_DISJUNCT_SORTING ) {
//		    stats = abox.getDisjBranchStats().get(disjunction);    
//		    if(stats == null) {
//		        int preference = preferredDisjunct();
//		        stats = new int[disj.length];
//		        for(int i = 0; i < disj.length; i++) {
//		            stats[i] = (i != preference) ? 0 : Integer.MIN_VALUE;
//		        }
//		        abox.getDisjBranchStats().put(disjunction, stats); 
//		    }
//		    if(getTryNext() > 0) {
//		        stats[order[getTryNext()-1]]++;
//			}
//			if(stats != null) {
//			    int minIndex = getTryNext();
//			    int minValue = stats[getTryNext()];
//		        for(int i = getTryNext() + 1; i < stats.length; i++) {
//		            boolean tryEarlier = ( stats[i] < minValue );		                
//		            
//		            if( tryEarlier ) {
//		                minIndex = i;
//		                minValue = stats[i];
//		            }
//		        }
//		        if(minIndex != getTryNext()) {
//		            ATermAppl selDisj = disj[minIndex];
//		            disj[minIndex] = disj[getTryNext()];
//		            disj[getTryNext()] = selDisj;
//		            order[minIndex] = getTryNext();
//		            order[getTryNext()] = minIndex;	            
//		        }
//			}
//		}
		
		Node node = this.node.getSame();

		for(; getTryNext() < getTryCount(); tryNext++) {
			ATermAppl d1 = notDisj[getTryNext()][0];
			ATermAppl d2 = notDisj[getTryNext()][1];

			if(PelletOptions.USE_SEMANTIC_BRANCHING) {
				for(int m = 0; m < getTryNext(); m++)
					strategy.addType(node, ATermUtils.negate( notDisj[m][0] ), prevDS[m]);
			}

			DependencySet ds = null;
			if(getTryNext() == getTryCount() - 1 && !PelletOptions.SATURATE_TABLEAU) {
				ds = getTermDepends();
				for(int m = 0; m < getTryNext(); m++)
					ds = ds.union(prevDS[m], abox.doExplanation());

				//CHW - added for incremental reasoning and rollback through deletions
				if(PelletOptions.USE_INCREMENTAL_DELETION)
					ds.setExplain( getTermDepends().getExplain() );
				else
					ds.remove(getBranch());
			}
			else {
				//CHW - Changed for tracing purposes
				if(PelletOptions.USE_INCREMENTAL_DELETION)
					ds = getTermDepends().union(new DependencySet(getBranch()), abox.doExplanation());
				else{
					ds = new DependencySet(getBranch());
					//added for tracing
					Set<ATermAppl> explain = new HashSet<ATermAppl>();
					explain.addAll(getTermDepends().getExplain());
					ds.setExplain( explain );											
				}
            }
            
			if( log.isLoggable( Level.FINE ) ) 
                log.fine( getDebugMsg() );		
			
			ATermAppl notD1 = ATermUtils.qcNegate(d1);
			ATermAppl notD2 = ATermUtils.qcNegate(d2);
			DependencySet clashDepends1 = PelletOptions.SATURATE_TABLEAU ? null : node.getDepends(notD1);
			DependencySet clashDepends2 = PelletOptions.SATURATE_TABLEAU ? null : node.getDepends(notD2);
			if(clashDepends1 == null && clashDepends2 == null) {
			    strategy.addType(node, d1, ds);
			    strategy.addType(node, d2, ds);
				// we may still find a clash if concept is allValuesFrom
				// and there are some conflicting edges
				if(abox.isClosed()) {
					clashDepends1 = abox.getClash().getDepends();
					clashDepends2 = abox.getClash().getDepends();
				}	
			}
			else if (clashDepends1 == null){
			    clashDepends2 = clashDepends2.union(ds, abox.doExplanation());
			}
			else if (clashDepends2 == null) {
				clashDepends1 = clashDepends1.union(ds, abox.doExplanation());
			}
			else {
				clashDepends1 = clashDepends1.union(ds, abox.doExplanation());
			    clashDepends2 = clashDepends2.union(ds, abox.doExplanation());
			}
			
			// if there is a clash
			if(clashDepends1 != null || clashDepends2 != null) {				
				if( log.isLoggable( Level.FINE ) ) {
					Clash clash = abox.isClosed() ? abox.getClash() : Clash.atomic(node, (clashDepends1 == null)? clashDepends2 : clashDepends1, (clashDepends1 == null)? d2 : d1);
                    log.fine("CLASH: Branch " + getBranch() + " " + clash + "!" + " " + ((clashDepends1 == null)? clashDepends2.getExplain() : clashDepends1.getExplain() ) );
				}
				
				if( PelletOptions.USE_DISJUNCT_SORTING ) {
				    if(stats == null) {
				        stats = new int[notDisj.length];
				        for(int i = 0; i < notDisj.length; i++)
				            stats[i] = 0;
				        abox.getDisjBranchStats().put(disjunction, stats); 
				    }
					stats[order[getTryNext()]]++;
				}
				
				// do not restore if we do not have any more branches to try. after
				// backtrack the correct branch will restore it anyway. more
				// importantly restore clears the clash info causing exceptions
				boolean hasClashBranch = clashDepends1.contains(getBranch()) || clashDepends2.contains(getBranch());
				if(getTryNext() < getTryCount() - 1 && hasClashBranch) {
				    // do not restore if we find the problem without adding the concepts 
				    if(abox.isClosed()) {
				    	if( node.isLiteral() ) {
				    		abox.setClash( null );
				    		
				    		node.restore( branch );				    					    		
				    	}
				    	else {
							// restoring a single node is not enough here because one of the disjuncts could be an 
						    // all(r,C) that changed the r-neighbors
					        strategy.restoreLocal((Individual) node, this);
							
							// global restore sets the branch number to previous value so we need to
							// increment it again
							abox.incrementBranch();
				    	}
				    }
					
                    setLastClash( (clashDepends1 == null)? clashDepends2: clashDepends1 );
				}
				else {
				    // set the clash only if we are returning from the function
					if(abox.doExplanation()) {
						if( clashDepends1 != null ) {
							ATermAppl positive = (ATermUtils.isQcNot(notD1) ? d1 : notD1);
							abox.setClash(Clash.atomic(node, clashDepends1.union(ds, abox.doExplanation()), positive));
						}	
						if (clashDepends2 != null ) {
							ATermAppl positive = (ATermUtils.isQcNot(notD2) ? d2 : notD2);
							abox.setClash(Clash.atomic(node, clashDepends2.union(ds, abox.doExplanation()), positive));
						}
					}
					else {
						if( clashDepends1 != null )	
						    abox.setClash(Clash.atomic(node, clashDepends1.union(ds, abox.doExplanation())));
						if( clashDepends2 != null )
							abox.setClash(Clash.atomic(node, clashDepends2.union(ds, abox.doExplanation())));
					}
						
					//CHW - added for inc reasoning
					if(PelletOptions.USE_INCREMENTAL_DELETION)
						abox.getKB().getDependencyIndex().addCloseBranchDependency(this, abox.getClash().getDepends());

			        return;
				}
			} 
			else 
				return;
		}
		
		// this code is not unreachable. if there are no branches left restore does not call this 
		// function, and the loop immediately returns when there are no branches left in this
		// disjunction. If this exception is thrown it shows a bug in the code.
		throw new InternalReasonerException("This exception should not be thrown!");
	}
	
	
	/**
	 * Added for to re-open closed branches.
	 * This is needed for incremental reasoning through deletions
	 * 
	 * @param index The shift index
	 */
	public void shiftTryNext(int openIndex){
		//save vals
////		int ord = order[openIndex];
//		ATermAppl dis = disj[openIndex];
////		DependencySet preDS = prevDS[openIndex];
//
//		//TODO: also need to handle semantic branching	
//		if(PelletOptions.USE_SEMANTIC_BRANCHING){
////			if(this.ind.getDepends(ATermUtils.makeNot(dis)) != null){
////				//check if the depedency is the same as preDS - if so, then we know that we added it
////			}
//		}
//		
//		//need to shift both prevDS and next and order
//		//disjfirst
//		for(int i = openIndex; i < disj.length-1; i++){
//			disj[i] = disj[i+1];
//			prevDS[i] = prevDS[i+1];
//			order[i] = order[i];
//		}
//
//		//move open label to end
//		disj[disj.length-1] = dis;
//		prevDS[disj.length-1] = null;
//		order[disj.length-1] = disj.length-1;
//		
//		//decrement trynext
//		setTryNext( getTryNext() - 1 );		
	}
	
	
	/**
	 * 
	 */
	public void printLong(){
		for(int i = 0; i < notDisj.length; i++){
			System.out.println("Disj[" + i + "] " + notDisj[i][0] +" , "+ notDisj[i][1]);
			System.out.println("prevDS[" + i + "] " + prevDS[i]);
			System.out.println("order[" + i + "] " + order[i]);
		}

		//decrement trynext
		System.out.println("trynext: " + getTryNext());
	}

	/**
	 * @param disj the disj to set
	 */
	public void setDisj(ATermAppl[][] notDisj) {
		this.notDisj = notDisj;
	}

	/**
	 * @return the disj
	 */
//	public ATermAppl getDisjunct(int i) {
//		return disj[i];
//	}
}
