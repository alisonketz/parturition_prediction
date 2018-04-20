###################################################################################################
###
### Production_detector.R
### Alison Ketz
### 4/18/2018
###
###################################################################################################

production = function(d,eps,pw=126){

  d=as.data.frame(d)
  nCovs = dim(d)[2]-2
  id = unique(d[,1])
  nInd=length(id)
  ci = 3:dim(d)[2]
  
  if(length(eps)!=nCovs){cat("length(epsilon) != number features, try again \n");return}
  
  #Check for individual case, run production detection on single individuals only
  if(length(nInd)>1){cat("\n Cannot run anomaly detection on multiple individuals at once, try again \n");return}
  
  d.temp=d[d[,2]>=pw,]
  n.temp=dim(d.temp)[1]
    
  if(nCovs==1){#nInd = 1, ncovs=1
      ind.mean = mean(d[d[,2]<pw,ci],na.rm=TRUE)
      ind.sd =  sd(d[d[,2]<pw,ci],na.rm=TRUE)
      detect.quant = qnorm(eps,ind.mean,ind.sd)
      threshold.density = dnorm(detect.quant,ind.mean,ind.sd)
      threshold.p = pnorm(detect.quant,mean=ind.mean,sd=ind.sd)
      lower.prob=pnorm(d.temp[,ci],mean=ind.mean,sd=ind.sd)
      detect.density = dnorm(d.temp[,ci],ind.mean,ind.sd)
      hits.indx = which(is.finite(detect.density) & detect.density<=threshold.density)
      outs.indx = which(!(1:n.temp %in% hits.indx))
      alarm = list(rbind(d.temp[hits.indx,]))

      results.prob=data.frame(matrix(NA,nr=n.temp,nc=4))
      names(results.prob)=c("Result","Prob","Julian","Date")
      results.prob[,3]=d.temp[,2]
      results.prob[,4]=as.Date(d.temp[,2],origin="2018-01-01")
      results.prob[hits.indx,1]="Hit"
      results.prob[outs.indx,1]="Out"
      results.prob[hits.indx,2]=1-(lower.prob[hits.indx]/threshold.p)
      results.prob[outs.indx,2] =1-(1-lower.prob[outs.indx])/(1-threshold.p)
      
      for(i in 1:n.temp){
        if(results.prob[i,2]<0){
          results.prob[i,2] =1-(1-lower.prob[i])/(1-threshold.p)
          results.prob[i,1] ="Out*"
        }
      }
      
    }#end nInd=1,nCovs=1
    else {# if nInd=1 nCovs >1
      
      ind.mean = apply(d[d[,2]<pw,ci],2,mean,na.rm=TRUE)
      ind.sd = apply(d[d[,2]<pw,ci],2,sd,na.rm=TRUE)
      Sigma=diag(ind.sd)
      detect.quant=rep(NA,nCovs)
      for(i in 1:nCovs){
          detect.quant[i]=qnorm(eps[i],ind.mean[i],ind.sd[i])
      }
      threshold.density = dmvnorm(detect.quant,ind.mean,Sigma)
      threshold.p = pmvnorm(lower=rep(-Inf,nCovs),upper=detect.quant,mean=ind.mean,sigma=Sigma)[1]
      detect.density = rep(NA,n.temp)
      lower.prob=rep(NA,n.temp)
      for(i in 1:n.temp){
          up=as.numeric(d.temp[i,ci])
          up.na=is.na(up)
          detect.density[i] = dmvnorm(up[!up.na],ind.mean[!up.na],diag(ind.sd[!up.na]))
          lower.prob[i]=pmvnorm(lower=rep(-Inf,nCovs-sum(up.na)),upper = up[!up.na],mean=ind.mean[!up.na],sigma=diag(ind.sd[!up.na]))[1]
      }
      
      # hits.indx = which(is.finite(detect.density) & detect.density<=threshold.density & lower.prob <= threshold.p)
      hits.indx = which(is.finite(detect.density) & detect.density<=threshold.density)
      
      outs.indx = which(!(1:n.temp %in% hits.indx))
      alarm=list(rbind(d.temp[hits.indx,]))
      
      results.prob=data.frame(matrix(NA,nr=n.temp,nc=4))
      names(results.prob)=c("Result","Prob","Julian","Date")
      results.prob[,3]=d.temp[,2]
      results.prob[,4]=as.Date(d.temp[,2],origin="2018-01-01")
      results.prob[hits.indx,1]="Hit"
      results.prob[outs.indx,1]="Out"
      results.prob[hits.indx,2]=1-(lower.prob[hits.indx]/threshold.p)
      results.prob[outs.indx,2] =1-(1-lower.prob[outs.indx])/(1-threshold.p)
      
      for(i in 1:n.temp){
        if(results.prob[i,2]<0){
          results.prob[i,2] =1-(1-lower.prob[i])/(1-threshold.p)
          results.prob[i,1] ="Out*"
        }#end if
      }#end for
    }#end else nCovs>1,nInd = 1

    hit.today=results.prob[n.temp,1]=="Hit"

    return(list(results.prob=results.prob,
                detect.quant=detect.quant,
                threshold.density=threshold.density,
                threshold.p=threshold.p,
                detect.density=detect.density,
                lower.prob=lower.prob,
                hits.indx=hits.indx,
                outs.indx=outs.indx,
                hit.today=hit.today,
                id=id))
  
}#end production function