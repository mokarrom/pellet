package org.mindswap.pellet.tableau.completion.rule;

import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.logging.Level;

import org.mindswap.pellet.DependencySet;
import org.mindswap.pellet.Edge;
import org.mindswap.pellet.EdgeList;
import org.mindswap.pellet.Individual;
import org.mindswap.pellet.Node;
import org.mindswap.pellet.PelletOptions;
import org.mindswap.pellet.Role;
import org.mindswap.pellet.exceptions.InternalReasonerException;
import org.mindswap.pellet.tableau.completion.CompletionStrategy;
import org.mindswap.pellet.tableau.completion.queue.NodeSelector;
import org.mindswap.pellet.utils.ATermUtils;

import aterm.ATerm;
import aterm.ATermAppl;
import aterm.ATermList;

public class NotSomeValuesRule extends AbstractTableauRule {
	
	public NotSomeValuesRule(CompletionStrategy strategy) {
		super( strategy, NodeSelector.UNIVERSAL, BlockingType.NONE );
	}
	
	public  void apply( Individual x ) {
        List<ATermAppl> notSomeValues = x.getTypes( Node.NOTSOME );
        int size = notSomeValues.size();
        Iterator<ATermAppl> i = notSomeValues.iterator();
        while( i.hasNext() ) {
            ATermAppl nsv = i.next();
            DependencySet nsvDepends = x.getDepends( nsv );

            if(!PelletOptions.MAINTAIN_COMPLETION_QUEUE && nsvDepends == null)
				continue;
            
            applyNotSomeValues( x, nsv, nsvDepends );

            if( x.isMerged() || strategy.getABox().isClosed() )
                return;

            // if there are self links through transitive properties restart
            if( size != notSomeValues.size() ) {
                i = notSomeValues.iterator();
                size = notSomeValues.size();
            }
        }
    }
	
	/**
     * Apply the notSomeValues rule for the given type with the given dependency. The concept is in the
     * form qcnot(not(all(p. not(c)))) and this function adds qcnot (C) to all r-neighbors of x
     * 
     * @param x
     * @param nsv
     * @param ds
     */
    public void applyNotSomeValues( Individual x, ATermAppl nsv, DependencySet ds ) {
        // Timer timer = kb.timers.startTimer("applyAllValues");

//        if( nsv.getArity() == 0 )					//[TODO]: Temporarily commented.
//            throw new InternalReasonerException();
    	// notSomeValues is now in the normalized form qcnot( not(all(p. not(c))) )
    	ATermAppl a = (ATermAppl) nsv.getArgument(0);	//now, a = not(all(p. not(c)))
    	ATermAppl b = (ATermAppl) a.getArgument(0);		//now, b = all(p. not(c))
        ATerm p = b.getArgument( 0 );
        ATermAppl c = (ATermAppl) b.getArgument( 1 ); 
        c = ATermUtils.qcNegate( ATermUtils.negate( c ) ); 	// now c is qcnot(c)
        
        ATermList roleChain = ATermUtils.EMPTY_LIST;
        Role s = null;
        if( p.getType() == ATerm.LIST ) {
            roleChain = (ATermList) p;
            s = strategy.getABox().getRole( roleChain.getFirst() );
            roleChain = roleChain.getNext();
        }
        else
            s = strategy.getABox().getRole( p );

        if ( s.isTop() && s.isObjectRole() ) {
        	applyNotSomeValuesTop( nsv, c, ds );
        	return;
        }

        EdgeList edges = x.getRNeighborEdges( s );
        for( int e = 0; e < edges.size(); e++ ) {
            Edge edgeToY = edges.edgeAt( e );
            Node y = edgeToY.getNeighbor( x );
            DependencySet finalDS = ds.union( edgeToY.getDepends(), strategy.getABox().doExplanation() );
            
            if( roleChain.isEmpty() )
                applyNotSomeValues( x, s, y, c, finalDS );
            else if(y.isIndividual()) {
                ATermAppl allRC = ATermUtils.makeAllValues( roleChain, c );

                strategy.addType( y, allRC, finalDS );
            }

            if( x.isMerged() || strategy.getABox().isClosed() )
                return;
        }

        if( !s.isSimple() ) {
            Set<ATermList> subRoleChains = s.getSubRoleChains();
            for( Iterator<ATermList> it = subRoleChains.iterator(); it.hasNext(); ) {
                ATermList chain = it.next();
                DependencySet subChainDS = ds.union(s.getExplainSub(chain), strategy.getABox().doExplanation() );
				if (!applyNotSomeValuesPropertyChain(x, chain, c, subChainDS))
					return;
            }
        }
        
        if (!roleChain.isEmpty()) {
        	applyNotSomeValuesPropertyChain(x, (ATermList) p, c, ds);
        }

        // timer.stop();
    }
    
    protected boolean applyNotSomeValuesPropertyChain( Individual x, ATermList chain, ATermAppl c, DependencySet ds ) {
        Role r = strategy.getABox().getRole( chain.getFirst() );
        
        EdgeList edges = x.getRNeighborEdges( r );
        if( !edges.isEmpty() ) {
            ATermAppl allRC = ATermUtils.makeAllValues( chain.getNext(), c );

            for( int e = 0; e < edges.size(); e++ ) {
                Edge edgeToY = edges.edgeAt( e );
                Node y = edgeToY.getNeighbor( x );
                DependencySet finalDS = ds.union( edgeToY.getDepends(), strategy.getABox().doExplanation() );
                
                applyNotSomeValues( x, r, y, allRC, finalDS );

                if( x.isMerged() || strategy.getABox().isClosed() )
                    return false;
            }
        }
        
        return true;
   }
   
   protected void applyNotSomeValues( Individual subj, Role pred, Node obj, ATermAppl c, DependencySet ds ) {
       if( !obj.hasType( c ) ) {
           if( log.isLoggable( Level.FINE ) ) {
               log.fine( "NOTSOME : " + subj + " -> " + pred + " -> " + obj + " : " + ATermUtils.toString( c ) + " - " + ds );
           }

           //because we do not maintain the queue it could be the case that this node is pruned, so return
           if(PelletOptions.USE_COMPLETION_QUEUE && !PelletOptions.MAINTAIN_COMPLETION_QUEUE && obj.isPruned())
           	return;
           

           strategy.addType( obj, c, ds );
       }
   }
   

   public void applyNotSomeValues( Individual subj, Role pred, Node obj, DependencySet ds ) {
       List<ATermAppl> notSomeValues = subj.getTypes( Node.NOTSOME );
       int notSomeValuesSize = notSomeValues.size();
       Iterator<ATermAppl> i = notSomeValues.iterator();
       while( i.hasNext() ) {
           ATermAppl nsv = i.next();
	           
	       // notSomeValues is now in the normalized form qcnot( not(all(p. not(c))) )
	       ATermAppl a = (ATermAppl) nsv.getArgument(0);	//now, a = not(all(p. not(c)))
	       ATermAppl b = (ATermAppl) a.getArgument(0);		//now, b = all(p. not(c))
           ATerm p = b.getArgument( 0 );
           ATermAppl c = (ATermAppl) b.getArgument( 1 ); 
           c = ATermUtils.qcNegate( ATermUtils.negate( c ) ); 	// now c is qcnot(c)
           
           ATermList roleChain = ATermUtils.EMPTY_LIST;
           Role s = null;
           if( p.getType() == ATerm.LIST ) {
               roleChain = (ATermList) p;
               s = strategy.getABox().getRole( roleChain.getFirst() );
               roleChain = roleChain.getNext();
           }
           else
               s = strategy.getABox().getRole( p );
                       
           if ( s.isTop() && s.isObjectRole() ) {
           	applyNotSomeValuesTop( nsv, c, ds );
           	if( strategy.getABox().isClosed() )
                   return;
           	continue;
           }

           if( pred.isSubRoleOf( s ) ) {
               DependencySet finalDS = subj.getDepends( nsv );
				finalDS = finalDS.union( ds, strategy.getABox().doExplanation() );
				finalDS = finalDS.union( s.getExplainSubOrInv( pred ), strategy.getABox().doExplanation() );
               if( roleChain.isEmpty() )
                   applyNotSomeValues( subj, s, obj, c, finalDS );
               else if (obj.isIndividual()) {
                   ATermAppl allRC = ATermUtils.makeAllValues( roleChain, c );

                   strategy.addType( obj, allRC, finalDS );
               }
               
               if( strategy.getABox().isClosed() )
                   return;
           }

           if( !s.isSimple() ) {
               DependencySet finalDS = subj.getDepends( nsv ).union( ds, strategy.getABox().doExplanation() );
               Set<ATermList> subRoleChains = s.getSubRoleChains();
               for( Iterator<ATermList> it = subRoleChains.iterator(); it.hasNext(); ) {
                   ATermList chain = it.next();
                   
//                   if( !pred.getName().equals( chain.getFirst() ) )
                   Role firstRole = strategy.getABox().getRole(chain.getFirst());
                   if( !pred.isSubRoleOf( firstRole ) )
                       continue;

                   ATermAppl allRC = ATermUtils.makeAllValues( chain.getNext(), c );

                   applyNotSomeValues( subj, pred, obj, allRC, finalDS.union(
                   		firstRole.getExplainSub(pred.getName()), strategy.getABox().doExplanation()).union(
                   				s.getExplainSub(chain), strategy.getABox().doExplanation() ) );

                   if( subj.isMerged() || strategy.getABox().isClosed() )
                       return;
               }
           }

           if( subj.isMerged() )
               return;

           obj = obj.getSame();

           // if there are self links then restart
           if( notSomeValuesSize != notSomeValues.size() ) {
               i = notSomeValues.iterator();
               notSomeValuesSize = notSomeValues.size();
           }
       }
   }
   
   /**
    * Apply all values restriction for the Top object role
    */
   void applyNotSomeValuesTop( ATermAppl allTopC, ATermAppl c, DependencySet ds ) {
		for( Node node : strategy.getABox().getNodes() ) {
			if( node.isIndividual() && !node.isPruned() && !node.hasType( c ) ) {
				node.addType( c, ds );
				node.addType( allTopC, ds );
				
				if( strategy.getABox().isClosed() )
					break;
			}
		}
		
   }

}
