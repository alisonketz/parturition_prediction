############################################################################################################
###
### rundetector.R
### Alison C. Ketz
### 4/3/2017
###
############################################################################################################


############################################################################################################
###
### This Rscript does the following operations
###
### Read data
### Format data
### Project data
### obtain features
### run anomaly detection functions
### compile list of individuals giving birth
### emailing list to 
###
############################################################################################################

rm(list=ls())

###
### Load Libraries
###
.libPaths("C:/Users/ketza/Documents/R/win-library/3.4")
library(lubridate)
library(adehabitatLT)
library(geosphere)
library(mvtnorm)
library(xtable)
library(rmarkdown)
library(ggplot2)
library(rgdal)
library(pander)
library(gmailr)

setwd("C:/Users/ketza/Documents/parturition_prediction")

### load mortality data (to make list of individuals who have died)
###
load("morts.Rdata")

startdate = "2018-03-15 00:00:00 CDT"

###
### set working directory to where the data csv files are
###

setwd('C:/Users/ketza/Documents/GPS_Lotek/Position Data')

###
### Read data 
###

datalist_temp = list.files(pattern="*.CSV")
myfiles = lapply(datalist_temp, read.csv,header=TRUE,stringsAsFactors=FALSE)
notlive=unlist(lapply(myfiles,function(x){x[1,1]}))#remove collars not on deer yet
datalist_temp=datalist_temp[-which(is.na(notlive))]
myfiles = lapply(datalist_temp, read.csv,header=TRUE,stringsAsFactors=FALSE)
nameHeader = tolower(gsub('[[:punct:]]',"",names(myfiles[[1]])))

#reset wd
setwd("C:/Users/ketza/Documents/parturition_prediction")

#clean data
datafiles=lapply(myfiles,function(x){
  names(x)<-nameHeader #fix column names, remove punctuation
  x[,1]<-trimws(x[,1]) #trimwhitespace in deviceid column
  lowtag=rep(substr(x[1,1], 1, 4),dim(x)[1])
  x=data.frame(lowtag,x,stringsAsFactors = FALSE)
  x})

#get list of all ids
# datafiles=lapply(datafiles,function(x){lowtag=rep(substr(x[1,1], 1, 4),dim(x)[1]);x=data.frame(lowtag,x,stringsAsFactors = FALSE);x})
ids=unlist(lapply(datafiles,function(x){x[1,1]}))

#remove morts from overall list of dataframes
datafiles[which(ids %in% morts)]=NULL


#get list of remaining alive ids
ids=unlist(lapply(datafiles,function(x){x[1,1]}))


#remove individuals with messed up GPS collars
badcollars=c(5884,6044,7237,5173,5107,5740,5078,6884,5900,5720,6847,6821)

datafiles[which(ids %in% badcollars)]=NULL

#get list of remaining individuals to run through detector
ids=unlist(lapply(datafiles,function(x){x[1,1]}))

miss.long=sapply(datafiles,function(x){sum(x$longitude==0)})
miss.lat = sapply(datafiles,function(x){sum(x$latitude==0)})

miss.gps=data.frame(ids,miss.long)
save(miss.gps,file=paste("Results/",Sys.Date(),"-",format(Sys.time(),"%p"),"-miss.gps.Rdata",sep=""))

#removing bad GPS fixes where DOP >10
datafiles=lapply(datafiles,function(x){
  x=x[x$dop<10,]
  x
})

x=datafiles[[1]]
miss.latest=sapply(datafiles,function(x){
  x$date_time_local=as.POSIXct(x$datetimegmt*60*60*24, tz = "CST6CDT", origin = "1899-12-30")
  x$julian=yday(x$date_time_local)
  temp=tail(unique(x$julian),2)
  y=sum(x[x$julian==temp[1] |x$julian==temp[2],7]==0)
  y
})

datafiles=lapply(datafiles,function(x){
  
    #remove observations with 0 long/lat
    x=x[x$longitude!=0,]
    x=x[x$latitude!=0,]

    #impute missing values of lat/long using geosphere midpoint
    if(sum(is.na(x$longitude))==0){x=x}#check if any missing values
    else{
      for(i in 2:(dim(x)[1]-1)){
        if(is.na(x$longitude[i])){
          a=i-1
          while(is.na(x$longitude[a])){a=a-1}
          b=i+1
          while(is.na(x$longitude[b])){b=b+1}
          save = midPoint(cbind(x$longitude[a],x$latitude[a]),cbind(x$longitude[b],x$latitude[b]))
          x$longitude[i] = save[1]
          x$latitude[i] = save[1]
        }
      }
    }#end missing values

    # creating date/time columns, converting julian dates
    x$date_time_gmt=as.POSIXct(x$datetimegmt*60*60*24, tz = "GMT", origin = "1899-12-30")
    x$date_time_local=as.POSIXct(x$datetimegmt*60*60*24, tz = "CST6CDT", origin = "1899-12-30")

    #Create time lag between successive locations and add as column to all dataframes
    timediff= diff(x[,5])*24
    x=x[-1,]
    x=data.frame(x,timediff,stringsAsFactors = FALSE)


    #calculate bearings
    x$bear=bearing(cbind(x$longitude,x$latitude))

    #calculate distances and step rate
    dist.out = distHaversine(cbind(x$longitude,x$latitude))
    x=x[-1,]
    x$distance = dist.out
    x$step = x$distance/x$timediff

    #remove observations prior to start date of spring tracking comparison 
    ### for wtd = March 15, 2018
    x=x[x$date_time_local>startdate,]

    #julian day
    x$julian=yday(x$date_time_local)
x
})#end function #endlapply

### remove individuals without observations since spring start date
sizes=lapply(datafiles,function(x){
  dim(x)[1]
})
sizes=unlist(sizes)

removed.indx=which(sizes==0)
removed=ids[removed.indx]
removed 
datafiles[which(sizes==0)]=NULL
miss.latest=miss.latest[-removed.indx]
ids=ids[-removed.indx]

save(removed,file=paste("Results/",Sys.Date(),"-",format(Sys.time(),"%p"),"-removed.init.Rdata",sep=""))


#project data 
#calculate and compile adehabitat features

datafiles=lapply(datafiles,function(x){

    # setup coordinates
    coords = cbind(x$longitude, x$latitude)
    sp = SpatialPoints(coords)

    # make spatial data frame
    # spdf = SpatialPointsDataFrame(coords, x)
    spdf = SpatialPointsDataFrame(sp, x)

    # EPSG strings
    latlong = "+init=epsg:4326"
    proj4string(spdf) = CRS(latlong)

    x.sp.proj = spTransform(spdf, CRS("+proj=tmerc +lat_0=0 +lon_0=-90 +k=0.9996 +x_0=520000+y_0=-4480000 +ellps=GRS80 +towgs84=0,0,0,0,0,0,0 +units=m +no_defs"))
    x=data.frame(x.sp.proj)

    #load into adehabitat
    x.traj <- as.ltraj(cbind(x$coords.x1,x$coords.x2), date=x$date_time_local,id=x$lowtag)

    #converts traj object to data frame
    x.traj.df = ld(x.traj)
    x.traj.df$id=as.character(x.traj.df$id)
    x.traj.df=rbind(rep(NA,dim(x.traj.df)[2]),x.traj.df)
    x.traj.df=x.traj.df[-dim(x.traj.df)[1],]
    x$relangle=x.traj.df$rel.angle
    x$disttraj=x.traj.df$dist
    x$R2n=x.traj.df$R2n
    x$dx=x.traj.df$dx
    x$dy=x.traj.df$dy

    remove.indx=which(is.na(x$disttraj))
    x <- x[-remove.indx,]
    x
})

#two day moving window summary statistics, centered and scaled, returns list of matrixes of all the features
#first column is id
#second column is julian day

features=lapply(datafiles,function(x){
    julian.temp = unique(x$julian)
    x.covs = matrix(NA,nr = length(julian.temp),nc = 18)
    x.covs[,1]=as.numeric(x$lowtag[1])
    x.covs[,2]=julian.temp
    for(i in 1:length(julian.temp)){
            x.covs[i,3] = mean(x$step[x$julian == julian.temp[i] | x$julian == (julian.temp[i]-1)],na.rm=TRUE)#mu.step
            x.covs[i,4] = sd(x$step[x$julian == julian.temp[i] | x$julian == (julian.temp[i]-1)],na.rm=TRUE)#sig.step
            x.covs[i,5] = mean(x$altitude[x$julian == julian.temp[i] | x$julian == (julian.temp[i]-1)],na.rm=TRUE)#mu.altitude
            x.covs[i,6] = sd(x$altitude[x$julian == julian.temp[i] | x$julian == (julian.temp[i]-1)],na.rm=TRUE)#sig.altitude
            x.covs[i,7] = mean(x$tempc[x$julian == julian.temp[i] | x$julian == (julian.temp[i]-1)],na.rm=TRUE)#mu.temp
            x.covs[i,8] = sd(x$tempc[x$julian == julian.temp[i] | x$julian == (julian.temp[i]-1)],na.rm=TRUE)#sig.temp
            x.covs[i,9] = mean(x$bear[x$julian == julian.temp[i] | x$julian == (julian.temp[i]-1)],na.rm=TRUE)#mu.bearing
            x.covs[i,10] = sd(x$bear[x$julian == julian.temp[i] | x$julian == (julian.temp[i]-1)],na.rm=TRUE)#sig.bearing
            x.covs[i,11] = mean(x$relangle[x$julian == julian.temp[i] | x$julian == (julian.temp[i]-1)],na.rm=TRUE)#mu.rel.angle
            x.covs[i,12] = sd(x$relangle[x$julian == julian.temp[i] | x$julian == (julian.temp[i]-1)],na.rm=TRUE)#sig.rel.angle
            x.covs[i,13] = mean(x$R2n[x$julian == julian.temp[i] | x$julian == (julian.temp[i]-1)],na.rm=TRUE)#mu.R2n
            x.covs[i,14] = sd(x$R2n[x$julian == julian.temp[i] | x$julian == (julian.temp[i]-1)],na.rm=TRUE)#sig.R2n
            x.covs[i,15] = mean(x$dx[x$julian == julian.temp[i] | x$julian == (julian.temp[i]-1)],na.rm=TRUE)#mu.dx
            x.covs[i,16] = sd(x$dx[x$julian == julian.temp[i] | x$julian == (julian.temp[i]-1)],na.rm=TRUE)#sig.dx
            x.covs[i,17] = mean(x$dy[x$julian == julian.temp[i] | x$julian == (julian.temp[i]-1)],na.rm=TRUE)#mu.dy
            x.covs[i,18] = sd(x$dy[x$julian == julian.temp[i] | x$julian == (julian.temp[i]-1)],na.rm=TRUE)#sig.dy
    }
    x.covs[,3:18]=apply(x.covs[,3:18],2,scale)
    x.covs
})

nInd.collared=length(features)

#parturition window date
#May 1
pw.julian=yday("2018-05-01")

### remove individuals without observations since spring start date
maxdates=sapply(features,function(x){
  max(x[,2])
})
maxdates=unlist(maxdates)

missed.latest=miss.latest[-which(maxdates<pw.julian)]
id.notrun=sapply(features[which(maxdates<pw.julian)],function(x){
	x[1,1]})
date.notrun=as.character(as.Date(maxdates[which(maxdates<pw.julian)],origin="2017-12-31"))

notrun.df=data.frame(id.notrun,date.notrun)
save(notrun.df,file=paste("Results/",Sys.Date(),"-",format(Sys.time(),"%p"),"-notrun.df.Rdata",sep=""))

features[which(maxdates<pw.julian)]=NULL
nInd.run = length(features)


load('epsilon.Rdata')

###
### running across subset of individuals using lapply
### easily extendable to all individuals
###

# yday("2018-05-10) #this will be the parturition window julian day

source("production_detector.R")

out=lapply(features,function(x){
  production(x,eps=epsilon,pw=pw.julian)
})

hits = sapply(out,function(x){x$hit.today})
hits.today = ifelse(hits,'Hit','Out')
results.prob.sum = sapply(out,function(x){tail(x$results.prob,1)[,2]})
threshold.p.sum = sapply(out,function(x){x$threshold.p})
lower.p.sum = sapply(out,function(x){tail(x$lower.prob,1)})
last.julian.obs = sapply(out,function(x){tail(x$results.prob,1)[,3]})
last.date.obs=sapply(out,function(x){y=tail(x$results.prob,1)[,4];as.character(y)})
id = as.factor(sapply(out,function(x){x$id}))


#email body text output

if(sum(hits)==0){
  body.out="No Predicted Births Today"
}else{
  body.out= paste("Lowtag of predicted births: \n",paste(as.character(id[hits]),collapse="\n"),sep="")
}


#data frame subsets of results for output in report

cbPalette <- c("#999999", "#E69F00", "#56B4E9", "#009E73", "#F0E442", "#0072B2", "#D55E00", "#CC79A7")

pw = yday("2018-05-01")
julian.today = yday(Sys.Date())
end = yday("2018-06-30")
Day = rep(pw:end,nInd.run)
ID = sort(rep(id,length(pw:end)))


hit.df=data.frame(Day,ID)
hit.mat = matrix(0,ncol=(end-pw+1),nrow=nInd.run)
for(j in 1:nInd.run){
    if(dim(out[[j]]$alarm)[1]!=0){
      hit.mat[j,(out[[j]]$alarm[,2] - pw+1)] = 1
    }
}

hit.mat=cbind(as.numeric(as.character(id)),hit.mat)
hit.mat=hit.mat[order(hit.mat[,1]),]
hit.mat=hit.mat[,-1]

face=c()
for(k in 1:floor(nInd.run/30)){
  face=c(face,rep(k,30*length(pw:end)))
}
face=c(face,rep(floor(nInd.run/30)+1,(nInd.run%%30)*length(pw:end)))

hit.df$face=face
hit.df$Hit = c(t(hit.mat))
hit.df$IDnumeric=hit.df$ID
hit.df$ID = as.factor(hit.df$ID)

save(hit.df,file=paste("Results/",Sys.Date(),"-",format(Sys.time(),"%p"),"-hit.df.Rdata",sep=""))

length(id)
length(missed.latest)

#dataframe output of anomaly detection results for individuals run
out.df=data.frame(id,hits.today,last.julian.obs,last.date.obs,results.prob.sum,threshold.p.sum,lower.p.sum,missed.latest,stringsAsFactors = FALSE)

#subset of individuals who's latest observation was not today's date, or yesterdays date
not.out.df = out.df[out.df$last.julian.obs!=julian.today & out.df$last.julian.obs!=(julian.today-1),]

#fixing and formatting out.df
hits.out=hits[out.df$last.julian.obs==julian.today| out.df$last.julian.obs==(julian.today-1)]
out.df = out.df[out.df$last.julian.obs==julian.today| out.df$last.julian.obs==(julian.today-1),]
out.df$hits.today=as.factor(out.df$hits.today)
out.df$id=as.factor(out.df$id)

#fixing and formatting not.out.df
#length(out[which(id %in% not.out.df$id)])
latest.result=lapply(out[which(id %in% not.out.df$id)],function(x){
  tail(x$results.prob,1)[1]
})
latest.result=as.character(unlist(latest.result))
not.out.df$hits.today=latest.result

save(out.df,file=paste("Results/",Sys.Date(),"-",format(Sys.time(),"%p"),"-resultsout.Rdata",sep=""))
save(not.out.df,file=paste("Results/",Sys.Date(),"-",format(Sys.time(),"%p"),"-notresultsout.Rdata",sep=""))

###
### If individuals were out today due to no data even though they were run through the anomaly detector, then here are the results in plot form for the day before today
### The following is a summary of recent results of those individuals


# alarm.indx=which(id %in% not.out.df[,1])
# alarm.out=do.call(rbind,lapply(out[alarm.indx],function(x){x$alarm}))
# subs=which(alarm.out[,2]==(julian.today-2))
# results.prob.out=lapply(out[alarm.indx],function(x){x$results.prob})
# results.prob.out[!(1:length(alarm.indx) %in% subs)]=NULL
# lower.prob.out=lapply(out[alarm.indx],function(x){tail(x$lower.prob,1)})
# lower.prob.out[!(1:length(alarm.indx) %in% subs)]=NULL
# lp=do.call(rbind,lower.prob.out)
# thresh.prob.out=lapply(out[alarm.indx],function(x){x$threshold.p})
# thresh.prob.out[!(1:length(alarm.indx) %in% subs)]=NULL
# th.p=do.call(rbind,thresh.prob.out)
# priorday=cbind(alarm.out[subs,1],do.call(rbind,lapply(results.prob.out,function(x){tail(x,1)})),lp,th.p)
# if(dim(priorday)[1]!=0){
#   names(priorday)=c("ID","Result","Prob","Julian","Date","lower.prob","th.p")
#   priorday=priorday[order(priorday$ID),]
# }else{
#   priorday = "No prior day hits to show"
# }
# 
# save(priorday,file=paste("Results/",Sys.Date(),"-",format(Sys.time(),"%p"),"-priorday.Rdata",sep=""))
# 

########################################################################################
###
### Render pdf document and email results
###
###
########################################################################################

rmarkdown::render("Report_Generation.Rmd",output_file=paste(Sys.Date(),"-",format(Sys.time(),"%p"),"-Prediction-Report.pdf",sep=""),output_dir = "Results")

html_msg_attach <- mime() %>%
  to(c("aketz@wisc.edu",
	"DanielJ.Storm@wisconsin.gov",
	"dwalsh@usgs.gov",
	"Wesley.Ellarson@wisconsin.gov",
	"Katie.Luukkonen@wisconsin.gov",
	"Logan.Hahn@wisconsin.gov",
	"Dana.Jarosinski@wisconsin.gov",
	"Hannah.Manninen@wisconsin.gov")) %>%
  from("wtdparturition@gmail.com") %>%
  subject(paste("Prediction Results",Sys.Date(),"-",format(Sys.time(),"%p"))) %>%
  html_body(print(body.out))%>%
  attach_part(print(body.out)) %>%
  attach_file(paste("C:/Users/ketza/Documents/parturition_prediction/Results/",Sys.Date(),"-",format(Sys.time(),"%p"),"-Prediction-Report.pdf",sep=""))

send_message(html_msg_attach)


###
### Email addresses to send prediction results report
###
#	
