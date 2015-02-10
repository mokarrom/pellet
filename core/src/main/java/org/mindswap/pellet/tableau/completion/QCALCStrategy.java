package org.mindswap.pellet.tableau.completion;

import java.util.logging.Level;

import org.mindswap.pellet.ABox;
import org.mindswap.pellet.IndividualIterator;
import org.mindswap.pellet.PelletOptions;
import org.mindswap.pellet.tableau.branch.Branch;
import org.mindswap.pellet.tableau.completion.rule.TableauRule;

import com.clarkparsia.pellet.expressivity.Expressivity;

public class QCALCStrategy extends CompletionStrategy {

	public QCALCStrategy(ABox abox) {
		super( abox );
	}
	
	protected boolean backtrack() {
		
		return false;
	}
	
	public void complete(Expressivity expr) {
		initialize( expr );
		
		while( !abox.isComplete() ) {
			while( abox.isChanged() && !abox.isClosed() ) {
				completionTimer.check();

				abox.setChanged( false );

				if( log.isLoggable( Level.FINE ) ) {
					log.fine( "Branch: " + abox.getBranch() + ", Depth: " + abox.stats.treeDepth
							+ ", Size: " + abox.getNodes().size() + ", Mem: "
							+ (Runtime.getRuntime().freeMemory() / 1000) + "kb" );
					abox.validate();
					printBlocked();
					abox.printTree();
				}

				IndividualIterator i = (PelletOptions.USE_COMPLETION_QUEUE)
					? abox.getCompletionQueue()
					: abox.getIndIterator();

				// flush the queue
				if( PelletOptions.USE_COMPLETION_QUEUE )
					abox.getCompletionQueue().flushQueue();

				for( TableauRule tableauRule : tableauRules ) {
					tableauRule.apply( i );
					if( abox.isClosed() )
						break;
				}

				// it could be the case that there was a clash and we had a
				// deletion update that retracted it
				// however there could have been some thing on the queue that
				// still needed to be refired from backtracking
				// so onle set that the abox is clash free after we have applied
				// all the rules once
				if( PelletOptions.USE_COMPLETION_QUEUE )
					abox.getCompletionQueue().setClosed( abox.isClosed() );
			}

			if( abox.isClosed() ) {
				if( log.isLoggable( Level.FINE ) )
					log.fine( "Clash at Branch (" + abox.getBranch() + ") " + abox.getClash() );

				if( backtrack() ) {
					abox.setClash( null );

					if( PelletOptions.USE_COMPLETION_QUEUE )
						abox.getCompletionQueue().setClosed( false );
				}
				else {
					abox.setComplete( true );

					// we need to flush the queue to add the other elements
					if( PelletOptions.USE_COMPLETION_QUEUE )
						abox.getCompletionQueue().flushQueue();
				}
			}
			else {
				if( PelletOptions.SATURATE_TABLEAU ) {
					Branch unexploredBranch = null;
					for( int i = abox.getBranches().size() - 1; i >= 0; i-- ) {
						unexploredBranch = abox.getBranches().get( i );
						unexploredBranch.setTryNext( unexploredBranch.getTryNext() + 1 );
						if( unexploredBranch.getTryNext() < unexploredBranch.getTryCount() ) {
							restore( unexploredBranch );
							System.out.println( "restoring branch " + unexploredBranch.getBranch()
									+ " tryNext = " + unexploredBranch.getTryNext()
									+ " tryCount = " + unexploredBranch.getTryCount() );
							unexploredBranch.tryNext();
							break;
						}
						else {
							System.out.println( "removing branch " + unexploredBranch.getBranch() );
							abox.getBranches().remove( i );
							unexploredBranch = null;
						}
					}
					if( unexploredBranch == null ) {
						abox.setComplete( true );
					}
				}
				else
					abox.setComplete( true );
			}
		}
	}//end complete 
	
}//end QCALCStrategy

