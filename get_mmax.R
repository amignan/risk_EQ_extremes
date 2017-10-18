#Copyright (c) 2017 Arnaud Mignan
  
#  Permission is hereby granted, free of charge, to any person obtaining a copy
#of this software and associated documentation files (the "Software"), to deal
#in the Software without restriction, including without limitation the rights
#to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
#copies of the Software, and to permit persons to whom the Software is
#furnished to do so, subject to the following conditions:
  
#  The above copyright notice and this permission notice shall be included in all
#copies or substantial portions of the Software.

#THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
#IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
#FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
#AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
#LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
#OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
#SOFTWARE.
#--------------------------------------------------------------------------------


#1. Computes the longest possible earthquake rupture lengths Lmax from a set of
#fault segments of lengths L & strike-slip mechanisms
#2. Convert Lmax into maximum magnitude Mmax
#
#DEPENDENCIES:
#fault segment data folder to be uploaded first in the inputs folder
#region = "ESHM13": FSBGmodelv6.1 data folder (European Seismic Hazard Model 2013)
# from SHARE project (ESHM13 DB) publicly available at:
# http://portal.share-eu.org/en/Documentation/specific-hazard-models/europe/active-faults/
#region = "EMME": emme_fs_model data folder (Middle East Seismic Hazard Model)
# not public yet
#
#CITATION:
#Mignan, A., L. Danciu & D. Giardini (2015), Reassessment of the Maximum Fault
#Rupture Length of Strike-Slip Earthquakes and Inference on Mmax in the 
#Anatolian Peninsula, Turkey, Seismol. Res. Lett., 86, 890-900, doi: 
#10.1785/0220140252


#LIBRARIES
rm(list=ls())
library(shapefiles) #read.shapefile()
library(maps)
library(mapdata)
library(ggplot2)
library(ggmap)
library(reshape2)   #melt()
library(gridExtra)  #grid.arrange()
library(splancs)    #inpip()


#FUNCTIONS
lon_km <- function(lat){
	rad_earth <- 6378.1   #km
	return(rad_earth*cos(lat*pi/180)*pi/180)
}

mech <- function(rake){
	indR <- which(rake > 45 & rake < 135)
	indN <- which(rake > 225 & rake < 315)
	indLL <- which(rake >= 315 | rake <= 45)
	indRL <- which(rake >= 135 & rake <= 225)
	res <- character(length(rake))
	if(length(indR) != 0) res[indR] <- "R"
	if(length(indN) != 0) res[indN] <- "N"
	if(length(indLL) != 0) res[indLL] <- "LL"
	if(length(indRL) != 0) res[indRL] <- "RL"
	return(res)
}

col_mech <- function(rake){
	indR <- which(rake > 45 & rake < 135)
	indN <- which(rake > 225 & rake < 315)
	indLL <- which(rake >= 315 | rake <= 45)
	indRL <- which(rake >= 135 & rake <= 225)
	col_mech <- character(length(rake))
	col_mech[indR] <- "red"
	col_mech[indN] <- "gold"
	col_mech[indLL] <- "yellow"
	col_mech[indRL] <- "orange"
	return(col_mech)
}

L2M <- function(L,W){
  A <- L*W
  #Wells & Coppersmith (1994) Table 2A for SS
  aWC <- 5.16; bWC <- 1.12
  m.WC <- aWC+bWC*log10(L)
  #Mai & Beroza (2000)
  aMB <- -5.15; bMB <- 0.36
  logM0 <- (log10(L)-aMB)/bMB    # [N.m]
  m.MB <- 0.67*(logM0+7)-10.7  #Hanks & Kanamori (1979)
  #Hanks & Bakun 2002 (SS)
  m.HB <- log10(A)+3.98
  m.HB[which(A > 537)] <- 4/3*log10(A[which(A > 537)])+3.07
  #Leonard (2010)  Table 6 (SS)
  aL <- 1.67; bL <- 4.17
  m.L <- aL*log10(L)+bL
  #Wesnousky 2008 SS
  m.W <- 5.56+0.87*log10(L)
  return(list(WC94=m.WC, MB00=m.MB, HB02=m.HB, L10=m.L, W08=m.W))
}

jump <- function(source.coord, source.param, init.coord, init.param, Delta){
	#create buffer around Delta ( rectangle ABCD per subsegment + tips made
  #of 3 points (oriented at 45??, 90??, 135??) approximating half a circle)
  #Delta=5km in theoretical case but depends in practice on fault DB resolution
	init.n <- nrow(init.coord)
	xstart <- init.coord$x[1]
	ystart <- init.coord$y[1]
	xend <- init.coord$x[init.n]
	yend <- init.coord$y[init.n]
	sign <- -(xend-xstart)/abs(xend-xstart)
	for(j in 1:(init.n-1)){
		x1 <- init.coord$x[j]
		y1 <- init.coord$y[j]
		x2 <- init.coord$x[j+1]
		y2 <- init.coord$y[j+1]
		alpha <- atan((y2-y1)/(x2-x1))
		xA <- x1+Delta*sin(alpha)/111
		xB <- x1-Delta*sin(alpha)/111
		yA <- y1-Delta*cos(alpha)/111
		yB <- y1+Delta*cos(alpha)/111
		if(j == 1){
			x45 <- x1+sign*Delta*cos(pi/4+alpha)/111
			y45 <- y1+sign*Delta*sin(pi/4+alpha)/111
			x90 <- x1+sign*Delta*cos(alpha)/111
			y90 <- y1+sign*Delta*sin(alpha)/111
			x135 <- x1+sign*Delta*cos(pi/4-alpha)/111
			y135 <- y1-sign*Delta*sin(pi/4-alpha)/111
			if(sign == 1){
				poly.x <- c(xB,x45,x90,x135,xA)
				poly.y <- c(yB,y45,y90,y135,yA)
			} else{
				poly.x <- c(xB,x135,x90,x45,xA)
				poly.y <- c(yB,y135,y90,y45,yA)
			}
		} else if(j == (init.n-1)){
			xD <- x2+Delta*sin(alpha)/111
			xC <- x2-Delta*sin(alpha)/111
			yD <- y2-Delta*cos(alpha)/111
			yC <- y2+Delta*cos(alpha)/111
			x45 <- x2-sign*Delta*cos(pi/4+alpha)/111
			y45 <- y2-sign*Delta*sin(pi/4+alpha)/111
			x90 <- x2-sign*Delta*cos(alpha)/111
			y90 <- y2-sign*Delta*sin(alpha)/111
			x135 <- x2-sign*Delta*cos(pi/4-alpha)/111
			y135 <- y2+sign*Delta*sin(pi/4-alpha)/111
			if(sign == -1){
				poly.x <- c(xC,xB,poly.x,xA,xD,x135,x90,x45,xC)
				poly.y <- c(yC,yB,poly.y,yA,yD,y135,y90,y45,yC)
			} else{
				poly.x <- c(xC,xB,poly.x,xA,xD,x45,x90,x135,xC)
				poly.y <- c(yC,yB,poly.y,yA,yD,y45,y90,y135,yC)
			}			
		} else{
			poly.x <- c(xB,poly.x,xA)
			poly.y <- c(yB,poly.y,yA)			
		}
	}

	#get faults in buffer
	indIN <- inpip(data.frame(x=source.coord$x, y=source.coord$y), data.frame(x=poly.x, y=poly.y))
	inddist <- unique(source.coord$id[indIN])
	if(round == 1) inddist <- inddist[-which(inddist == init.param$id)]
	if(round > 1){
		parts <- as.numeric(unlist(strsplit(init.param$parts, "-")))
		for(j in 1:length(parts)) inddist <- inddist[-which(inddist == parts[j])]
	}
	
	#remove parts with different mechanism
	n.jump <- length(inddist)
	if(n.jump > 0){
		mech.init <- mech(init.param$rake)
		mech.jump <- mech(source.param$rake[inddist])
		inddiff <- which(mech.jump != mech.init)
		if(length(inddiff) > 0) inddist <- inddist[-inddiff]

		#remove parts with different dip directions
		n.jump <- length(inddist)
		if(n.jump > 0){
			dipdir.init <- sign
			#WARNING: in case of cascades, sign does not match dip direction,
			#but depends on direction of propagation, eg. A+B or B+A
			#While originally a glitch, it permits to remove redundant cascades!
			#NB: the dip of cascades cannot be derived from sign
			dipdir.jump <- numeric(n.jump)
			for(j in 1:n.jump){
				indjump <- which(source.coord$id == inddist[j])
				jump.n <- length(indjump)
				xstart <- source.coord$x[indjump][1]
				ystart <- source.coord$y[indjump][1]
				xend <- source.coord$x[indjump][jump.n]
				yend <- source.coord$y[indjump][jump.n]
				dipdir.jump[j] <- -(xend-xstart)/abs(xend-xstart)
			}
			inddiff <- which(dipdir.jump != dipdir.init)
			if(length(inddiff) > 0) inddist <- inddist[-inddiff]
		}
	}
	
	pdf(paste(wd, "/", outd, "/1_dist_seg", init.param$id, ".pdf", sep=""))
	map('worldHires', xlim=c(region[1],region[2]), ylim=c(region[3],region[4]))
	for(j in 1:nflt.SS){
		lines(fltshp[[indregion.SS[j]]]$points, col="grey")
		if(length(which(inddist == j)) != 0) lines(fltshp[[indregion.SS[j]]]$points, col="red")
	}
	lines(init.coord$x, init.coord$y, col=col_mech(init.param$rake))
	polygon(poly.x, poly.y, border="black")
	map.axes()
	dev.off()

	return(list(inddist=inddist))
}

bendbranch <- function(source.coord, source.param, init.coord, init.param, inddist){
	alpha <- init.param$strike
	Psi <- (init.param$rake/2+45)%%90           #angle between segment & Smax direction
	gamma <- NA                                 #cases when rake not SS or LL-RL combined
	if(init.param$rake >= 135 & init.param$rake <= 225) gamma <- 1  #right-lateral
	if(init.param$rake >= 315 | init.param$rake <= 45) gamma <- -1  #left-lateral
	psi <- gamma*(45-Psi-180*atan(muD)/(2*pi))  #optimal angle for rupture, gamma=1 for RL

	ntarget <- length(inddist)
	beta <- numeric(ntarget)
	phi <- numeric(ntarget)
	propa <- character(ntarget)
	if(is.na(psi) == F) for(j in 1:ntarget){
		beta[j] <- source.param$strike[inddist[j]]
		phi[j] <- alpha-beta[j]
		if((phi[j] >= psi-delta) & (phi[j] <= psi+delta)) propa[j] <- "yes" else propa[j] <- "no"
	}
	indangle <- which(propa == "yes")
	if(length(indangle) > 0){
		pdf(paste(wd, "/", outd, "/2_angle_seg", init.param$id, ".pdf", sep=""))
		map('worldHires', xlim=c(region[1],region[2]), ylim=c(region[3],region[4]))
		for(j in 1:nflt.SS){
			lines(fltshp[[indregion.SS[j]]]$points, col="grey")
			if(length(which(inddist[indangle] == j)) != 0) lines(fltshp[[indregion.SS[j]]]$points, 
        col="red")
		}
		lines(init.coord$x, init.coord$y, col=col_mech(init.param$rake))
		map.axes()
		dev.off()
	}
	return(list(indangle=indangle))
}

propa <- function(source.coord, source.param, init.coord, init.param, inddist, indangle,
  id_new){
	A.n <- nrow(init.coord)
	ntarget <- length(indangle)

	list_xA <- init.coord$x       #source A (initiator)
	list_yA <- init.coord$y
	anchor_xA <- numeric(ntarget)
	anchor_yA <- numeric(ntarget)
	anchor_xB <- numeric(ntarget)
	anchor_yB <- numeric(ntarget)

	for(j in 1:ntarget){
		indB <- which(source.coord$id == inddist[indangle[j]])   #source B (propagator)
		B.n <- length(indB)
		list_xB <- source.coord$x[indB]
		list_yB <- source.coord$y[indB]

		#anchor points
		d <- numeric(A.n*B.n); dim(d) <- c(A.n,B.n)
		for(k in 1:A.n) d[k,] <- sqrt((list_xB-list_xA[k])^2+(list_yB-list_yA[k])^2)
		indanchor <- which(d == min(d), arr.ind=T)
		anchor_xA[j] <- list_xA[indanchor[1]]
		anchor_yA[j] <- list_yA[indanchor[1]]
		anchor_xB[j] <- list_xB[indanchor[2]]
		anchor_yB[j] <- list_yB[indanchor[2]]

		#join segments (A1-B1 / A1-B2 / A2-B1 / A2-B2)
		splitA1 <- unique(seq(1,indanchor[1]))
		splitA2 <- unique(seq(A.n,indanchor[1]))
		splitB1 <- unique(seq(indanchor[2],1))
		splitB2 <- unique(seq(indanchor[2], B.n))
			
		angleA1B1 <- NA; angleA1B2 <- NA; angleA2B1 <- NA; angleA2B2 <- NA
		if(length(splitA1) > 1 & length(splitB1) > 1) angleA1B1 <- 
		  (list_xA[splitA1[1]]-list_xA[splitA1[length(splitA1)]])/(list_xB[splitB1[1]]-
		    list_xB[splitB1[length(splitB1)]])
		if(length(splitA1) > 1 & length(splitB2) > 1) angleA1B2 <- 
		  (list_xA[splitA1[1]]-list_xA[splitA1[length(splitA1)]])/(list_xB[splitB2[1]]-
		    list_xB[splitB2[length(splitB2)]])
		if(length(splitA2) > 1 & length(splitB1) > 1) angleA2B1 <- 
		  (list_xA[splitA2[1]]-list_xA[splitA2[length(splitA2)]])/(list_xB[splitB1[1]]-
		    list_xB[splitB1[length(splitB1)]])
		if(length(splitA2) > 1 & length(splitB2) > 1) angleA2B2 <- 
		  (list_xA[splitA2[1]]-list_xA[splitA2[length(splitA2)]])/(list_xB[splitB2[1]]-
		    list_xB[splitB2[length(splitB2)]])
		path <- c(angleA1B1,angleA1B2,angleA2B1,angleA2B2)
		path.correct <- which(is.na(path) == F & path > 0)

		if(length(path.correct) > 0){
			if(length(path.correct) > 1){   #delete small bits of segment association
				tmpA1B1 <- length(splitA1)+length(splitB1)
				tmpA1B2 <- length(splitA1)+length(splitB2)
				tmpA2B1 <- length(splitA2)+length(splitB1)
				tmpA2B2 <- length(splitA2)+length(splitB2)
				tmp_length <- c(tmpA1B1,tmpA1B2,tmpA2B1,tmpA2B2)
				indmax <- which(tmp_length[path.correct] == max(tmp_length[path.correct]))
				path.correct <- path.correct[indmax]
			}

			if(path.correct == 1){
				list_xAB <- c(list_xA[splitA1], list_xB[splitB1]) 
				list_yAB <- c(list_yA[splitA1], list_yB[splitB1]) 
			}	
			if(path.correct == 2){
				list_xAB <- c(list_xA[splitA1], list_xB[splitB2]) 
				list_yAB <- c(list_yA[splitA1], list_yB[splitB2]) 
			}
			if(path.correct == 3){
				list_xAB <- c(list_xA[splitA2], list_xB[splitB1]) 
				list_yAB <- c(list_yA[splitA2], list_yB[splitB1]) 
			}
			if(path.correct == 4){
				list_xAB <- c(list_xA[splitA2], list_xB[splitB2]) 
				list_yAB <- c(list_yA[splitA2], list_yB[splitB2]) 
			}
		
			#create cascade source
			id_new <- id_new+1
			
			if(round == 1) partA <- init.param$id else partA <- init.param$parts
			parts <- paste(partA, "-", source.param$id[inddist[indangle[j]]], sep="")
			
			cascade.coord <- data.frame(id=id_new, x=list_xAB, y=list_yAB)
			cascade.param <- list(id=id_new, strike=(
			  init.param$strike+source.param$strike[inddist[indangle[j]]])/2,
			  rake=(init.param$rake+source.param$rake[inddist[indangle[j]]])/2, parts=parts)
			
			#save files
			write.table(cascade.coord, file=paste(wd, "/", outd, "/file_cascade_coord_", round, ".txt", sep=""), 
			  col.names=F, row.names=F, quote=F, append=T)
			write.table(cascade.param, file=paste(wd, "/", outd, "/file_cascade_param_", round, ".txt", sep=""),
			  col.names=F, row.names=F, quote=F, append=T)
		
			pdf(paste(wd, "/", outd, "/3_propa_seg", init.param$id, "_", id_new, ".pdf", sep=""))
			map('worldHires', xlim=c(region[1],region[2]), ylim=c(region[3],region[4]))
			for(j in 1:nflt.SS) lines(fltshp[[indregion.SS[j]]]$points, col="grey")
			lines(cascade.coord$x, cascade.coord$y, col="red")
			map.axes()
			dev.off()
		}
	}
	return(list(id_new=id_new))
}



## SETUP ##
wd <- getwd()
outd <- "outputs"
if(!file.exists(outd)) dir.create(outd)
figd <- "figures"
if(!file.exists(figd)) dir.create(figd)

rad_earth <- 6378.1         #km
lat_km <- rad_earth*pi/180  #assumed spherical

model <- "ESHM13"           #fault model: ESHM13, EMME14
region <- c(23,46,34,42)    #Anatolian region (minlon,maxlon,minlat,maxlat)
#region <- c(24,75,23.5,44.5)  #EMME14 region
Delta <- 5                 #max distance threshold (km), 5km by default but can be higher
muD <- 0.12                 #dynamic friction coeff.
delta <- 30                 #range of preferred orientation

nround <- 15                #maximum number of loops, nround approx. to no. of merged segments
npt <- 500                  #maximum number of points per cascade segment

#get fault model data
if(model == "ESHM13") flt <-
  read.shapefile(paste(wd,"/inputs/FSBGmodelv6.1/FSBGModelV6.1_FaultSources", sep=""))
  #List of column names:
  #IDBG IDSOURCE FAULTTYPE TECTOTYPE TECTOCODE TECREG PREFERRED MINDEPTH
  #MAXDEPTH STRIKEMIN STRIKEMAX DIPMIN DIPMAX RAKEMIN RAKEMAX MWORIGINAL MINMW
  #MAXMW RANGE MEANMW STDEVMW WMEANMW WSTDEVMW NMAGVAL MWDIFF TOTALL STRAIGHTL
  #TOTALW TOTALA STRAIGHTA ASPECTRATI EFFECTIVEA EFFECTIVEL SRMIN SRMAX
if(model == "EMME14") flt <-
  read.shapefile(paste(wd,"/inputs/emme_fs_model/fs_model_ver07", sep=""))
  #List of column names:
  #IDSOURCE FAULTTYPE   BGRVAL  AGRVAL TECTOTYPE RAKEMIN RAKEMAX DIPMIN DIPMAX STRIKEMIN
  #STRIKEMAX MINDEPTH MAXDEPTH UC_MIN MC_MIN   SRMIN   SRMAX SRMAX01 SRMAX02 SRMAX03
  #WSRMAX01 WSRMAX02 WSRMAX03  WSRMAX   MAXMAG ASPECTRATI CLASS    LENGTH     WIDTH
  #IDSOURCE_2  SRMIN_2  SRMAX_2  WMEANMW RP_GT7

fltshp <- flt$shp$shp
fltdbf <- flt$dbf$dbf
nflt <- dim(fltdbf)[1]
nparam <- dim(fltdbf)[2]
strike <- ((fltdbf$STRIKEMIN+fltdbf$STRIKEMAX)/2)%%180
rake <- (fltdbf$RAKEMIN+fltdbf$RAKEMAX)/2
dip <- (fltdbf$DIPMIN+fltdbf$DIPMAX)/2
sliprate <- (fltdbf$SRMIN+fltdbf$SRMAX)/2

#select fault segments from region
flt.minx <- numeric(nflt)
flt.maxy <- numeric(nflt)
for(i in 1:nflt){
	flt.minx[i] <- min(fltshp[[i]]$points$X)
	flt.maxy[i] <- max(fltshp[[i]]$points$Y)
}
indregion <- which(flt.minx > region[1] & flt.maxy < region[4])
nflt <- length(indregion)

n_pflt <- numeric(nflt)
flt <- data.frame(lon=c(),lat=c(),group=c())
for(i in 1:nflt){
  n_pflt[i] <- nrow(fltshp[[indregion[i]]]$points)
  flt <- rbind(flt, data.frame(lon=fltshp[[indregion[i]]]$points$X,
    lat=fltshp[[indregion[i]]]$points$Y, id=rep(i,n_pflt[i])))
}

#select Strike-Slip ruptures only
indregion.SS <- which(((rake >= 315 | rake <= 45) | (rake >= 135 & rake <= 225)) &
                        flt.minx > region[1] & flt.maxy < region[4])
nflt.SS <- length(indregion.SS)

n_pflt.SS <- numeric(nflt.SS)
flt.SS <- data.frame(lon=c(),lat=c(),group=c())
for(i in 1:nflt.SS){
  n_pflt.SS[i] <- nrow(fltshp[[indregion.SS[i]]]$points)
  flt.SS <- rbind(flt.SS, data.frame(lon=fltshp[[indregion.SS[i]]]$points$X,
                                     lat=fltshp[[indregion.SS[i]]]$points$Y, id=rep(i,n_pflt.SS[i])))
}


#map faults
marg <- ceiling((region[2]-region[1])/(region[4]-region[3]))  #googlemap rescaling - portrait case
map <- get_map(location=c(region[1]-marg,region[3]-marg,region[2]+marg,region[4]+marg),
  source='google', maptype='satellite', crop=T)

pdf(paste(wd, "/", figd,"/segments_Mech.pdf", sep=""))
g1 <- ggmap(map) +
  geom_path(data=flt, aes(x=lon, y=lat, group=id),
    colour=rep(col_mech(rake[indregion]),times=n_pflt), lwd=0.6) +
  scale_x_continuous("Longitude", limits=c(region[1],region[2])) +
  scale_y_continuous("Latitude", limits=c(region[3],region[4])) +
  labs(title="Map of fault mechanisms", subtitle=paste("Data: ", model, sep=""))

dat.mech <- data.frame(rake=rake[indregion], mech=mech(rake[indregion]))
g2 <- ggplot(data=dat.mech, aes(x=rake, fill=mech)) +
  geom_histogram(binwidth=10) +
  coord_polar() +
  scale_fill_manual(values=c("yellow","gold","red","orange")) +
  scale_x_continuous(limits=c(0,360)) +
  theme_minimal() +
  labs(title="Fault mechanism distribution", x=expression(paste("Rake (", degree, ")", sep="")),
    y="Number of segments", fill="Mechanism", subtitle="LL: left-lateral, N: normal,
    R: reverse, RL: right-lateral")

Psi <- (rake[indregion.SS]/2+45)%%90        #angle between segment & Smax direction
psi <- (45-Psi-180*atan(muD)/(2*pi))        #optimal angle for rupture, gamma=1 for RL
dat.dyn <- data.frame(psi=c(psi,psi-delta,psi+delta),
  range=c(rep("med",nflt.SS), rep("min",nflt.SS), rep("max",nflt.SS)))
g3 <- ggplot(data=dat.dyn, aes(x=psi, fill=range)) +
  geom_histogram(binwidth=10) +
  coord_polar() +
  scale_x_continuous(limits=c(-180,180)) +
  theme_minimal() +
  scale_fill_manual(expression(paste(phi, " range", sep="")), values=c("sienna3","sienna2","sienna1"),
    labels=c(expression(psi-delta),expression(psi),expression(psi+delta)),
    breaks=c("min","med","max")) +
  labs(title=expression(paste("Max. strike difference ", phi, " distribution"), sep=""),
    subtitle="Strike-slip only, LL & RL", x=expression(paste(phi, " (", degree, ")", sep="")),
    y="Number of segments")

grid.arrange(g1, arrangeGrob(g2,g3, ncol=2), nrow=2)
dev.off()



## generate cascades (SS only) ###
#get all subsegment coordinates for 1st round of calculation
list_x <- c()
list_y <- c()
list_id <- c()
for(i in 1:nflt.SS){
	list_x <- c(list_x, fltshp[[indregion.SS[i]]]$points$X)
	list_y <- c(list_y, fltshp[[indregion.SS[i]]]$points$Y)
	list_id <- c(list_id, rep(i, nrow(fltshp[[indregion.SS[i]]]$points)))
}
source.coord <- data.frame(id=list_id, x=list_x, y=list_y)
source.param <- list(id=seq(1,nflt.SS), strike=strike[indregion.SS], rake=rake[indregion.SS])
#rake 0-360 deg.; strike 0-180 deg.

#verify that output files do not exist (to avoid writing )
test <- paste(wd, "/", outd, "/file_cascade_coord_1.txt", sep="")
if(file.exists(test)) stop("Output files alreading existing. Please delete or change name")


#main loop : generate cascades
n <- nflt.SS
ntot <- 0                   #total number of cascades generated
for(round in 1:nround){
  id_new <- round*10000     #each new generation of cascades gets new set of IDs

  if(round > 1){
    cascade.coord.name <- paste(wd, "/", outd, "/file_cascade_coord_", round-1, ".txt", sep="")
    if(!file.exists(cascade.coord.name)) break
    #breaks from loop if no more cascades to define before nround
  	cascade.coord <- read.table(cascade.coord.name, header=F, col.names=c("id","x","y"))
  	cascade.param <- read.table(paste(wd, "/", outd, "/file_cascade_param_", round-1, ".txt", sep=""),
  	  header=F, col.names=c("id","strike","rake","parts"))
  	n <- nrow(cascade.param)
  	ntot <- ntot+n
  }

  for(i in 1:n){
  	print(paste(round, "/", i, "/", n))
  	#define source to propagate
  	if(round == 1){
  		indinit <- which(source.coord$id == i)
  		init.coord <- data.frame(id=source.coord$id[indinit], x=source.coord$x[indinit],
  		  y=source.coord$y[indinit])
  		indinit <- which(source.param$id == i)
  		init.param <- list(id=source.param$id[indinit], strike=source.param$strike[indinit],
  		  rake=source.param$rake[indinit])
  	}
  	if(round > 1){
  		indinit <- which(cascade.coord$id == i+(round-1)*10000)
  		init.coord <- unique( data.frame(id=cascade.coord$id[indinit], x=cascade.coord$x[indinit],
  		  y=cascade.coord$y[indinit]) )
  		indinit <- which(cascade.param$id == i+(round-1)*10000)
  		init.param <- list(id=cascade.param$id[indinit], strike=cascade.param$strike[indinit],
  		  rake=cascade.param$rake[indinit], parts=as.character(cascade.param$parts[indinit]))
  	}

  	## 1. jumping ##
  	res1 <- jump(source.coord, source.param, init.coord, init.param, Delta)

  	## 2. bending/branching ##
  	if(length(res1$inddist) > 0){
  		res2 <- bendbranch(source.coord, source.param, init.coord, init.param, res1$inddist)
	
  		## 3. rupture propagation ##
  		if(length(res2$indangle) > 0){
  			res3 <- propa(source.coord, source.param, init.coord, init.param, res1$inddist,
  			  res2$indangle, id_new)
  			id_new <- res3$id_new
  		}
  	}
  }
}
nround <- round-2


#check Lmax in cascade rounds
casc.L <- numeric(ntot)
casc.sliprate <- numeric(ntot)
casc.coord <- numeric(2*ntot*npt); dim(casc.coord) <- c(2,ntot,npt); casc.coord[,,] <- NA

kk <- 1
for(i in 1:nround){
	print(paste(i, "/", nround))
	cascade.coord <- read.table(paste(wd, "/", outd, "/file_cascade_coord_", i, ".txt",
	  sep=""), header=F, col.names=c("id","x","y"))
	cascade.param <- read.table(paste(wd, "/", outd, "/file_cascade_param_", i, ".txt",
	  sep=""), header=F, col.names=c("id","strike","rake","parts"))

	for(j in 1:nrow(cascade.param)){
		indj <- which(cascade.coord$id == cascade.param$id[j])
		n.coord <- length(indj)
		length.tmp <- 0
		for(k in 1:(n.coord-1)) length.tmp <- length.tmp+sqrt(((cascade.coord$x[indj][k+1]-
		  cascade.coord$x[indj][k])*lon_km(cascade.coord$y[indj][k]))^2+
		  ((cascade.coord$y[indj][k+1]-cascade.coord$y[indj][k])*lat_km)^2)
		casc.L[kk] <- length.tmp

		id_parts <- as.numeric(unlist(strsplit(as.character(cascade.param$parts[j]), "-")))
		tmp <- 0
		for(l in 1:length(id_parts)) tmp <- tmp+sliprate[id_parts[l]]
		casc.sliprate[kk] <- tmp/length(id_parts)
		casc.coord[1,kk,(1:length(indj))] <- cascade.coord$x[indj]
		casc.coord[2,kk,(1:length(indj))] <- cascade.coord$y[indj]
		
		kk <- kk+1
	}
}
#Relationship from Anderson et al. 1996
casc.M <- 5.12+1.16*log10(casc.L)-0.20*log10(casc.sliprate)



## plot results ##
if(model == "ESHM13"){
  orig.L <- fltdbf$TOTALL[indregion.SS]
  orig.Mmax <- fltdbf$MAXMW[indregion.SS]
  orig.W <- round(mean(fltdbf$TOTALW[indregion.SS]))
}
if(model == "EMME14"){
  orig.L <- fltdbf$LENGTH[indregion.SS]
  orig.Mmax <- fltdbf$MAXMAG[indregion.SS]
  orig.W <- round(mean(fltdbf$WIDTH[indregion.SS]))
}
orig.sliprate <- sliprate[indregion.SS]

#Mmax map (individual segments)
#Relationship from Anderson et al. 1996
orig.M <- 5.12+1.16*log10(orig.L)-0.20*log10(orig.sliprate)
flt.SS$Mmax <- rep(orig.M, times=n_pflt.SS)

plot.lmax <- max(casc.L)
plot.mmin <- min(orig.M)
plot.mmax <- max(casc.M)
dat.orig <- data.frame(L=orig.L, Mmax=orig.M)
dat.new <- data.frame(L=casc.L, Mmax=casc.M)
li <- seq(1,plot.lmax)
dat.rel <- L2M(li,orig.W)
dat.rel.long <- melt(dat.rel)
dat.rel.long$L <- rep(li, times=5)

pdf(paste(wd, "/", figd, "/segments_Mmax.pdf", sep=""))
g1 <- ggmap(map) +
  geom_path(data=flt.SS, aes(x=lon, y=lat, group=id, color=Mmax), lwd=0.6) +
  scale_color_gradient(low="yellow", high="brown", limits=c(plot.mmin,plot.mmax)) +
  scale_x_continuous("Longitude", limits=c(region[1],region[2])) +
  scale_y_continuous("Latitude", limits=c(region[3],region[4])) +
  labs(title="Map of individual segment ruptures", subtitle=paste("Data: ", model, sep=""),
    col=expression(M[max]))

g2 <- ggplot() +
  geom_point(data=dat.orig, aes(x=L, y=Mmax, col=Mmax), show.legend=F) +
  geom_path(data=dat.rel.long, aes(x=L, y=value, lty=L1), alpha=.2) +
  scale_x_continuous(limits = c(0, plot.lmax)) +
  scale_y_continuous(limits = c(plot.mmin, plot.mmax)) +
  scale_color_gradient(low="yellow", high="brown", limits=c(plot.mmin,plot.mmax)) +
  theme_minimal() +
  labs(title="Length-magnitude relationship", x="Rupture length (km)", y=expression(M[max]),
    subtitle="Conversion based on Anderson et al. (1996)", lty="Ref.")
grid.arrange(g1,g2, ncol=1, nrow=2)
dev.off()


#Mmax map (cascades)
n_pflt.cascSS <- numeric(ntot)
flt.cascSS <- data.frame(lon=c(),lat=c(),group=c())
for(i in 1:ntot){
  n_pflt.cascSS[i] <- length(which(is.na(casc.coord[1,i,]) == F))
  if(n_pflt.cascSS[i] > 0) flt.cascSS <- rbind(flt.cascSS,
    data.frame(lon=casc.coord[1,i,(1:n_pflt.cascSS[i])],
    lat=casc.coord[2,i,(1:n_pflt.cascSS[i])], id=rep(i,n_pflt.cascSS[i])))
}
flt.cascSS$Mmax <- rep(casc.M, times=n_pflt.cascSS)

#flt.cascSS_new <- flt.cascSS[order(flt.cascSS$Mmax),]     #supposed to map in Mmax order
pdf(paste(wd, "/", figd, "/cascades_Mmax.pdf", sep=""))
g1 <- ggmap(map) +
  geom_path(data=flt.cascSS, aes(x=lon, y=lat, group=id, color=Mmax), lwd=0.6) +
  scale_color_gradient(low="yellow", high="brown", limits=c(plot.mmin,plot.mmax)) +
  scale_x_continuous("Longitude", limits=c(region[1],region[2])) +
  scale_y_continuous("Latitude", limits=c(region[3],region[4])) +
  labs(title="Map of cascading ruptures", subtitle=paste("Data: ", model, sep=""),
    col=expression(M[max]))
g2 <- ggplot() +
  geom_point(data=dat.new, aes(x=L, y=Mmax, col=Mmax), show.legend=F) +
  geom_path(data=dat.rel.long, aes(x=L, y=value, lty=L1), alpha=.2) +
  scale_x_continuous(limits = c(0, plot.lmax)) +
  scale_y_continuous(limits = c(plot.mmin, plot.mmax)) +
  scale_color_gradient(low="yellow", high="brown", limits=c(plot.mmin,plot.mmax)) +
  theme_minimal() +
  labs(title="Length-magnitude relationship", x="Rupture length (km)", y=expression(M[max]),
       subtitle="Conversion based on Anderson et al. (1996)", lty="Ref.")
grid.arrange(g1,g2, ncol=1, nrow=2)
dev.off()

