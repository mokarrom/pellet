package org.mindswap.pellet.tableau.completion.rule;

import java.util.Iterator;
import java.util.List;

import org.mindswap.pellet.DependencySet;
import org.mindswap.pellet.Edge;
import org.mindswap.pellet.EdgeList;
import org.mindswap.pellet.Individual;
import org.mindswap.pellet.Node;
import org.mindswap.pellet.Role;
import org.mindswap.pellet.tableau.completion.CompletionStrategy;
import org.mindswap.pellet.utils.ATermUtils;

import aterm.ATerm;
import aterm.ATermAppl;

public class SimpleNotSomeValuesRule extends NotSomeValuesRule {
	
	public SimpleNotSomeValuesRule(CompletionStrategy strategy) {
		super( strategy);
	}
	
	@Override
	public void applyNotSomeValues(Individual x, ATermAppl nsv, DependencySet ds) {
		// notSomeValues is now in the normalized form qcnot( not(all(p. not(c))) )
    	ATermAppl a = (ATermAppl) nsv.getArgument(0);	//now, a = not(all(p. not(c)))
    	ATermAppl b = (ATermAppl) a.getArgument(0);		//now, b = all(p. not(c))
        ATerm p = b.getArgument( 0 );
        ATermAppl c = (ATermAppl) b.getArgument( 1 ); 
        c = ATermUtils.qcNegate( ATermUtils.negate( c ) ); 	// now c is qcnot(c)
		
		Role s = strategy.getABox().getRole( p );
		
		if ( s.isTop() && s.isObjectRole() ) {
        	applyNotSomeValuesTop( nsv, c, ds );
        	return;
        }
		
		EdgeList edges = x.getRNeighborEdges( s );
		for( int e = 0; e < edges.size(); e++ ) {
			Edge edgeToY = edges.edgeAt( e );
			Node y = edgeToY.getNeighbor( x );
			DependencySet finalDS = ds.union( edgeToY.getDepends(), strategy.getABox().doExplanation() );
			if( strategy.getABox().doExplanation() ) {
				Role edgeRole = edgeToY.getRole();
				DependencySet subDS = s.getExplainSubOrInv( edgeRole );
				finalDS = finalDS.union( subDS.getExplain(), true );
			}
			
			applyNotSomeValues( x, s, y, c, finalDS );

			if( x.isMerged() )
				return;
		}

		if( !s.isSimple() ) {
			for( Role r : s.getTransitiveSubRoles() ) {
				ATermAppl allRC = ATermUtils.makeAllValues( r.getName(), c );

				edges = x.getRNeighborEdges( r );
				for( int e = 0; e < edges.size(); e++ ) {
					Edge edgeToY = edges.edgeAt( e );
					Node y = edgeToY.getNeighbor( x );
					DependencySet finalDS = ds.union( edgeToY.getDepends(), strategy.getABox().doExplanation() );
					if( strategy.getABox().doExplanation() ) {
						finalDS = finalDS.union( r.getExplainTransitive().getExplain(), true );
						finalDS = finalDS.union( s.getExplainSubOrInv( edgeToY.getRole() ), true );
					}
					
					applyNotSomeValues( x, r, y, allRC, finalDS );

					if( x.isMerged() )
						return;
				}
			}
		}
	}

    @Override
	public void applyNotSomeValues( Individual subj, Role pred, Node obj, DependencySet ds) {
    	
		List<ATermAppl> notSomeValues = subj.getTypes( Node.NOTSOME );
		int size = notSomeValues.size();
		Iterator<ATermAppl> i = notSomeValues.iterator();
		while( i.hasNext() ) {
			ATermAppl nsv = i.next();	
			
			// notSomeValues is now in the normalized form qcnot( not(all(p. not(c))) )
	    	ATermAppl a = (ATermAppl) nsv.getArgument(0);	//now, a = not(all(p. not(c)))
	    	ATermAppl b = (ATermAppl) a.getArgument(0);		//now, b = all(p. not(c))
	        ATerm p = b.getArgument( 0 );
	        ATermAppl c = (ATermAppl) b.getArgument( 1 ); 
	        c = ATermUtils.qcNegate( ATermUtils.negate( c ) ); 	// now c is qcnot(c)
			
			Role s = strategy.getABox().getRole( p );
			
			if ( s.isTop() && s.isObjectRole() ) {
            	applyNotSomeValuesTop( nsv, c, ds );
            	continue;
            }
			
			if( pred.isSubRoleOf( s ) ) {
				DependencySet finalDS = ds.union(  subj.getDepends( nsv ), strategy.getABox().doExplanation() );
				if( strategy.getABox().doExplanation() )
					finalDS = finalDS.union( s.getExplainSubOrInv( pred ).getExplain(), true );
                
				applyNotSomeValues( subj, s, obj, c, finalDS );

				if( s.isTransitive() ) {
					ATermAppl allRC = ATermUtils.makeAllValues( s.getName(), c );
					finalDS = ds.union( subj.getDepends( nsv ), strategy.getABox().doExplanation() );
					if( strategy.getABox().doExplanation() )
						finalDS = finalDS.union(  s.getExplainTransitive().getExplain(), true );
					
					applyNotSomeValues( subj, s, obj, allRC, finalDS );
				}
			}

			// if there are self links through transitive properties restart
			if( size != notSomeValues.size() ) {
				i = notSomeValues.iterator();
				size = notSomeValues.size();
			}
		}
	}

}
