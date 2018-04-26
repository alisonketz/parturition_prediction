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
library(mailR)
library(rmarkdown)
library(ggplot2)
library(rgdal)

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
datafiles[which(sizes==0)]=NULL

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



### remove individuals without observations since spring start date
maxdates=sapply(features,function(x){
  max(x[,2])
})
maxdatess=unlist(maxdates)
features[which(maxdates<105)]=NULL

load('epsilon.Rdata')

###
### running across subset of individuals using lapply
### easily extendable to all individuals
###

yday("2018-04-15")
# [1] 105

source("production_detector.R")
out=lapply(features,function(x){
  production(x,eps=epsilon,pw=105)
})

hits = sapply(out,function(x){x$hit.today})
hits.today = ifelse(hits,'Hit','Out')
results.prob.sum = sapply(out,function(x){tail(x$results.prob,1)[,2]})
threshold.p.sum = sapply(out,function(x){x$threshold.p})
id = as.factor(sapply(out,function(x){x$id}))

par(mfrow=c(1,1))
out.df=data.frame(id,hits.today,results.prob.sum,threshold.p.sum)
pdf(paste(Sys.Date(),"-results-plot.pdf",sep=""))
ggplot(data=out.df,aes(x=id))+geom_point(aes(y=results.prob.sum,color=hits))+
  theme(panel.background = element_rect(fill="white",color="black"),
        panel.grid.major=element_line("grey90"),
        axis.text.x = element_text(angle=90))
dev.off()


if(sum(hits)==0){
  body.out="No Predicted Births Today"
}else{
  body.out= paste("Lowtag of predicted births: \n",paste(as.character(id[hits]),collapse="\n"),sep="")
}

save(out.df,file=paste("Results/",Sys.Date(),"-resultsout.Rdata",sep=""))

########################################################################################
###
### Render html document and email results
###
###
########################################################################################

rmarkdown::render("Report_Generation.Rmd",output_file=paste(Sys.Date(),"-Prediction-Report.pdf",sep=""))

# sender <- "alison.ketz@gmail.com" 
# recipients <- c("alison.ketz@gmail.com","aketz@wisc.edu") 
# email <- send.mail(from = sender,
#                    to = recipients,
#                    subject=paste("Prediction Results",Sys.Date()),
#                    body = print(body.out),
#                    smtp = list(host.name = "aspmx.l.google.com", port = 25),
#                    authenticate = FALSE,
#                    attach.files = paste(getwd(),"/",Sys.Date(),"-Prediction-Report.pdf",sep="") ,
#                    debug=FALSE,
#                    send = TRUE)

sender <- "aketz@wisc.edu" 
recipients <- c("alison.ketz@gmail.com","aketz@wisc.edu") 
sapply(recipients,function(x){send.mail(from = sender,
                   to = x,
                   subject=paste("Prediction Results",Sys.Date()),
                   body = print(body.out),
                   smtp = list(host.name = "smtp.office365.com",port=587,user.name="aketz@wisc.edu",passwd="Recess$5505",tls=TRUE),
                   authenticate = TRUE,
                   attach.files = paste("C:/Users/ketza/Documents/parturition_prediction/Results/",Sys.Date(),"-Prediction-Report.pdf",sep="") ,
                   debug=FALSE,
                   send = TRUE)})

